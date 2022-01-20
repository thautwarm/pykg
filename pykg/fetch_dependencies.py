from __future__ import annotations
from ast import And
from operator import is_
from threading import local
from tkinter import Pack
from .async_request import (
    areadpage,
    run_many,
    gather_with_limited_workers,
    create_file_url,
)
from .data_reflection import to_comf, from_comf
from .component import Commented, operator
from .git import get_git_repo
from .project import (
    Project,
    Metadata,
    Dep,
    Url,
    create_metadata_from_project,
)
from .version import mk_version
from .classified_url import (ClassifiedUrl, CloudGitRepoUrl, CloudMetaUrl, CloudProjUrl, LocalMetaUrl, LocalProjUrl, classify_url)
from . import log
from . import git
from . import pretty_doc as doc
from .errors import InvalidComfigVersion
from .version import Version as version
from .z3_dep_solver import lt_tuple, le_tuple, gt_tuple, ge_tuple, eq_tuple, ne_tuple
from .z3_dep_solver import (
    get_major as _get_major,
    get_micro as _get_micro,
    get_minor as _get_minor,
)
from .z3_dep_solver import tuple_var as _tuple_var, TupleCons as _TupleCons
from collections import OrderedDict, deque
from pathlib import Path
from dataclasses import dataclass
import z3
import re
import typing
import sys

PackageId = str


class DefaultDict(dict):
    def __init__(self, f):
        self.f = f

    def __missing__(self, key):
        v = self[key] = self.f()
        return v


DEFAULT_MIRROR = r"https://raw.githubusercontent.com/thautwarm/comf-index/main"


def request_pykg(mirror: str, package_name: str, locals: dict[PackageId, ClassifiedUrl]):
    is_project = False
    if url_o := locals.get(package_name):
        if isinstance(url_o, LocalProjUrl):
            resp, src = yield from areadpage(create_file_url(url_o.project_comf_path))
            is_project = True
        elif isinstance(url_o, LocalMetaUrl):
            resp, src = yield from areadpage(create_file_url(url_o.meta_comf_path))
        elif isinstance(url_o, CloudMetaUrl):
            resp, src = yield from areadpage(url_o.link)
        elif isinstance(url_o, CloudProjUrl):
            resp, src = yield from areadpage(url_o.project_comf_url)
            is_project = True
        elif isinstance(url_o, CloudProjUrl):
            repo = git.get_git_repo(url_o, False)
            resp, src = yield from repo.areadfile("project.comf")
            is_project = True
        else:
            raise Exception(f"impossible: unknown url type: {url_o.__class__.__name__}")

        if resp.status != 200:
            raise ConnectionError(f"solving {package_name}: {url_o} is invalid")

        if is_project:
            proj = from_comf(Project, src.decode('utf-8'))
            new_locals, meta = create_metadata_from_project(url_o, proj)
            if new_locals:
                locals.update(new_locals)
        else:
            meta = from_comf(Metadata, src.decode('utf-8'))

        return meta
    kind, unkinded_name = package_name.split("/", 1)
    C = unkinded_name[0].upper()
    url = rf"{mirror}/{kind}/{C}/{unkinded_name}.comf"
    resp, comf = yield from areadpage(url)
    if resp.status != 200:
        raise ConnectionError(f"solving {package_name}: {url} is invalid")
    src = comf.decode("utf-8")
    try:
        return from_comf(Metadata, src)
    except InvalidComfigVersion as e:
        log.warn(
            f"invalid .comf from {url}: {e}\ncontact mirror maintainer to update the configuration."
        )
        return None
    except Exception as e:
        log.error(f"fatal error from .comf ({url}): " + str(e))
        raise


if not typing.TYPE_CHECKING:
    Z3Tuple = object
    Z3Int = object
    tuple_var = _tuple_var
    TupleCons = _TupleCons
    get_major = _get_major
    get_minor = _get_minor
    get_micro = _get_micro
else:
    Z3Tuple = typing.NewType("Z3Tuple", z3.AstRef)

    class Z3Int:
        def __add__(self, x: _int) -> Z3Int:
            ...

    _int = typing.Union[Z3Int, int]

    def get_major(x: Z3Tuple) -> Z3Int:
        ...

    def get_minor(x: Z3Tuple) -> Z3Int:
        ...

    def get_micro(x: Z3Tuple) -> Z3Int:
        ...

    def tuple_var(name: str) -> Z3Tuple:
        ...

    def TupleCons(major: _int, minor: _int, micro: _int) -> Z3Tuple:
        ...

    del _int


def patch_compare(x: Z3Tuple, y: Z3Tuple):
    upper_bound = TupleCons(get_major(y), get_minor(y) + 1, get_micro(y))
    return z3.And(ge_tuple(x, y), lt_tuple(x, upper_bound))


def compact_compare(x: Z3Tuple, y: Z3Tuple):
    upper_bound = TupleCons(get_major(y) + 1, 0, 0)
    return z3.And(ge_tuple(x, y), lt_tuple(x, upper_bound))


_op_maps: typing.Dict[operator, typing.Callable[[Z3Tuple, Z3Tuple], typing.Any]] = {
    operator.EQ: eq_tuple,
    operator.NE: ne_tuple,
    operator.LT: lt_tuple,
    operator.LE: le_tuple,
    operator.GT: gt_tuple,
    operator.GE: ge_tuple,
    operator.COMPACT: compact_compare,
    operator.PATCH: patch_compare,
}


def z3_tuple_to_version(x: Z3Tuple) -> version:
    major = z3.simplify(get_major(x)).as_long()  # type: ignore
    minor = z3.simplify(get_minor(x)).as_long()  # type: ignore
    micro = z3.simplify(get_micro(x)).as_long()  # type: ignore
    return mk_version(major, minor, micro)


def version_to_z3_tuple(x: version) -> Z3Tuple:
    return TupleCons(x.major, x.minor, x.micro)


def pretty_error(
    solver: z3.Solver,
    deps: _DepGraph,
    name_to_z3_tuple: dict[PackageId, Z3Tuple],
    meta: Metadata):
    return get_unsat_reason(solver, deps, name_to_z3_tuple, meta)

def get_unsat_reason(
    solver: z3.Solver,
    deps: _DepGraph,
    name_to_z3_tuple: dict[PackageId, Z3Tuple],
    meta: Metadata):

    n = len(meta.distributions) # n > 1
    n = min(10, n)
    unsat_cores = [ _get_unsat_reason(solver, deps, name_to_z3_tuple, meta, i) for i in range(n) ]
    return unsat_cores

def _get_unsat_reason(
    solver: z3.Solver,
    deps: _DepGraph,
    name_to_z3_tuple: dict[PackageId, Z3Tuple],
    meta: Metadata,
    i: int,
    ):
    solver.push()
    pid = meta.name.uncomment
    dist_ = meta.distributions[i]
    dist = dist_.uncomment
    z3_var_dep_ver = name_to_z3_tuple[pid]
    deps1 = deps[pid]
    deps2 = deps1[dist.version.uncomment]

    solver.assert_and_track(
        z3_var_dep_ver == version_to_z3_tuple(dist.version.uncomment),
        f"indirect dependency {pid} == {dist.version.uncomment}")
    for each_spec in dist.deps:
        dep_pid = each_spec.uncomment.name.uncomment
        if dep_pid in deps2:
            continue
        dep_var_ver = name_to_z3_tuple[dep_pid]
        for specifier in each_spec.uncomment.version.uncomment.specifiers:
            spec_ver = specifier.version
            z3_spec_ver = TupleCons(spec_ver.major, spec_ver.minor, spec_ver.micro)
            cmp_func = _op_maps[specifier.op]
            solver.assert_and_track(
                cmp_func(dep_var_ver, z3_spec_ver),
                f"{dep_pid} {specifier.op} {spec_ver}")


    solver.check()
    core = list(map(repr, solver.unsat_core())) # type: ignore
    solver.pop()
    return dist.version.uncomment, core



def update_deps_for_project(
    solver: z3.Solver,
    deps: _DepGraph,
    name_to_z3_tuple: dict[PackageId, Z3Tuple],
    meta: Metadata,
):
    pid = meta.name.uncomment
    deps1 = deps[pid]
    or_conditions = []
    for dist_ in meta.distributions:
        dist = dist_.uncomment
        deps2 = deps1[dist.version.uncomment]
        z3_var_dep_ver = name_to_z3_tuple[pid]
        dependency_constraints = [
            z3_var_dep_ver == version_to_z3_tuple(dist.version.uncomment)
        ]
        for each_spec in dist.deps:
            dep_pid = each_spec.uncomment.name.uncomment
            if dep_pid in deps2:
                log.warn(
                    f"{pid!r} depends on {dep_pid!r} more than once:\n{to_comf(each_spec.uncomment)}..."
                )
                continue
            deps2.add(dep_pid)
            dep_var_ver = name_to_z3_tuple[dep_pid]
            for specifier in each_spec.uncomment.version.uncomment.specifiers:
                spec_ver = specifier.version
                z3_spec_ver = TupleCons(spec_ver.major, spec_ver.minor, spec_ver.micro)
                cmp_func = _op_maps[specifier.op]
                dependency_constraints.append(cmp_func(dep_var_ver, z3_spec_ver))
            yield dep_pid
        or_conditions.append(z3.And(*dependency_constraints))
    solver.add(z3.Or(*or_conditions))


if typing.TYPE_CHECKING:
    _DepGraph = typing.Dict[PackageId, typing.Dict[version, typing.Set[PackageId]]]
    Formula = typing.NewType("Formula", z3.BoolRef)
else:
    _DepGraph = object


class DependencyUnsatisfied(Exception):
    direct_dep: str
    unsatisified_reasons: list[tuple[version, list[str]]]

    def __init__(self, direct_dep: str, indir: str, reasons: list[tuple[version, list[str]]]):
        self.direct_dep = direct_dep
        self.unsatisified_reasons = reasons
        msg = doc.vsep([
            doc.seg(f"directory dependency {direct_dep!r} is not satisfiable due to {indir!r}:"),
            doc.indent(2, doc.vsep([
                doc.vsep(
                    [
                        (doc.seg('==') + doc.seg(str(ver)) + doc.seg("invalid")),
                        doc.indent(4, doc.vsep(list(map(doc.seg, reason))))
                    ]
                )
                for ver, reason in reasons
            ]))
        ]).show()
        super().__init__(msg)


class PackageNameToZ3TupleVar(typing.Dict[PackageId, Z3Tuple]):
    def __missing__(self, key):
        v = self[key] = tuple_var(key)
        return v


@dataclass
class Requirements:
    self_meta: Metadata
    self_proj: typing.Optional[Project]
    locals: dict[PackageId, ClassifiedUrl]
    dependencies: dict[PackageId, tuple[Metadata, version]]  # ordered

    def get_dist(self, meta: Metadata):
        name = meta.name.uncomment
        _, v = self.dependencies[name]
        dist = find_dist_by_version(meta, v)
        if not dist:
            # TODO: what is an appropriate error here?
            raise Exception(f"dist not found for pykg '{name}' == {v}")
        return dist.uncomment


def get_deps_from_metadata(
    mirror: str, meta: Metadata, locals: dict[PackageId, ClassifiedUrl]
) -> Requirements:
    name_to_z3_tuple: PackageNameToZ3TupleVar = PackageNameToZ3TupleVar()
    dep_graph: _DepGraph = typing.cast(_DepGraph, DefaultDict(lambda: DefaultDict(set)))
    solver = z3.Solver()
    solver.push()
    requirements = list(
        update_deps_for_project(solver, dep_graph, name_to_z3_tuple, meta)
    )
    name_to_metadata: dict[PackageId, Metadata] = {meta.name.uncomment: meta}

    if solver.check() != z3.sat:
        solver.pop()
        raise DependencyUnsatisfied(meta.name.uncomment, meta.name.uncomment, pretty_error(solver, dep_graph, name_to_z3_tuple, meta))

    requirements_consumed = deque(requirements)
    reached: set[str] = {meta.name.uncomment}

    while requirements_consumed:
        requirement = requirements_consumed.popleft()
        to_resolve: list[str] = [requirement]
        while to_resolve:
            def comprehension():
                for pid in to_resolve:
                    if pid in reached:
                        continue
                    reached.add(pid)
                    yield request_pykg(mirror, pid, locals)

            tasks = list(comprehension())
            to_resolve.clear()
            metas = run_many(tasks)
            to_resolve = []
            for meta_ in metas:
                if meta_ is None:
                    continue
                name_to_metadata[meta_.name.uncomment] = meta_
                solver.push()
                assert solver.check() == z3.sat
                to_resolve.extend(
                    update_deps_for_project(solver, dep_graph, name_to_z3_tuple, meta_)
                )
                if solver.check() != z3.sat:
                    solver.pop()
                    raise DependencyUnsatisfied(requirement, meta_.name.uncomment, pretty_error(solver, dep_graph, name_to_z3_tuple, meta_))


    model = solver.model()

    # this procedure is to built correct order of fixed packages
    def get_version_of_package(pid):
        return z3_tuple_to_version(typing.cast(Z3Tuple, model[name_to_z3_tuple[pid]]))

    reached: set[PackageId] = set()

    def visit(pid: PackageId):
        if pid in reached:
            return
        ver = get_version_of_package(pid)
        reached.add(pid)
        dists = dep_graph[pid][ver]
        for dist in dists:
            yield from visit(dist)
        yield pid

    ordered_packages = list(visit(meta.name.uncomment))

    log.info(
        "dependencies resolved:\n" +
        '\n'.join(
            '- ' + name + " " + str(z3_tuple_to_version(model[name_to_z3_tuple[name]])) # type: ignore
        for name in ordered_packages))
    deps = OrderedDict()
    for pid in ordered_packages:
        deps[pid] = (name_to_metadata[pid], get_version_of_package(pid))
    return Requirements(meta, None, locals, deps)


def get_deps_from_local_project(
    mirror: str, project_path: str, proj: Project, locals: dict[PackageId, ClassifiedUrl]
):
    url_o = LocalProjUrl(project_path).cast()
    locals[proj.name.uncomment] = url_o
    # url_o = Url.raw_url(create_file_url(project_path))
    new_locals, meta = create_metadata_from_project(url_o, proj)
    if new_locals:
        locals.update(new_locals)
    locals[meta.name.uncomment] = url_o
    req = get_deps_from_metadata(mirror, meta, locals)
    req.self_proj = proj
    return req


def find_dist_by_version(meta: Metadata, ver: version):
    for dist in meta.distributions:
        dist_ver = dist.uncomment.version.uncomment
        if dist_ver == ver:
            return dist
    return None
