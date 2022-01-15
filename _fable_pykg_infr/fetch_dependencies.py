from __future__ import annotations
from ast import And
from tkinter import Pack
from .async_request import (
    get_async_result,
    areadpage,
    run_many,
    gather_with_limited_workers,
)
from _fable_pykg.src.proj import parse_metadata, metadata, serialize_dep
from _fable_pykg.src.comp import (
    FromCompinentError,
    mk_version,
    operator,
    specifier,
    uncomment,
)
from _fable_pykg.src import comp
from . import log
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
import z3
import re
import typing
import sys

from _fable_pykg_infr import z3_dep_solver


class DefaultDict(dict):
    def __init__(self, f):
        self.f = f

    def __missing__(self, key):
        v = self[key] = self.f()
        return v


DEFAULT_MIRROR = r"https://raw.githubusercontent.com/thautwarm/comf-index/main"


def request_pykg(mirror: str, package_name: str):
    kind, unkinded_name = package_name.split("/")
    C = unkinded_name[0].upper()
    url = rf"{mirror}/{kind}/{C}/{unkinded_name}.comf"
    resp, comf = yield from areadpage(url)
    if resp.status != 200:
        raise ConnectionError
    try:
        return parse_metadata(comf.decode("utf-8"))
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


_op_maps: typing.Dict[int, typing.Callable[[Z3Tuple, Z3Tuple], typing.Any]] = {
    id(comp.EQ): eq_tuple,
    id(comp.NE): ne_tuple,
    id(comp.LT): lt_tuple,
    id(comp.LE): le_tuple,
    id(comp.GT): gt_tuple,
    id(comp.GE): ge_tuple,
    id(comp.COMPACT): compact_compare,
    id(comp.PATCH): patch_compare,
}


def z3_tuple_to_version(x: Z3Tuple) -> version:
    major = z3.simplify(get_major(x)).as_long()  # type: ignore
    minor = z3.simplify(get_minor(x)).as_long()  # type: ignore
    micro = z3.simplify(get_micro(x)).as_long()  # type: ignore
    return mk_version(major, minor, micro)


def version_to_z3_tuple(x: version) -> Z3Tuple:
    return TupleCons(x.major, x.minor, x.micro)


PackageId = str


def update_deps_for_project(
    solver: z3.Solver,
    deps: _DepGraph,
    name_to_z3_tuple: dict[PackageId, Z3Tuple],
    # deps: dict[PackageId, dict[version, dict[PackageId, set[specifier]]]],
    meta: metadata,
):
    pid = uncomment(meta.name)
    deps1 = deps[pid]
    assert meta.distributions.elements is not None
    or_conditions = []
    for dist_ in meta.distributions.elements:
        dist = uncomment(dist_)
        deps2 = deps1[uncomment(dist.version)]
        z3_var_dep_ver = name_to_z3_tuple[pid]
        dependency_constraints = [
            z3_var_dep_ver == version_to_z3_tuple(uncomment(dist.version))
        ]
        assert dist.deps.elements is not None
        for each_spec_ in dist.deps.elements:
            each_spec = uncomment(each_spec_)
            dep_pid = each_spec.name
            deps2.add(dep_pid)
            dep_var_ver = name_to_z3_tuple[dep_pid]
            for specifier in uncomment(each_spec.version):
                spec_ver = specifier.version
                z3_spec_ver = TupleCons(spec_ver.major, spec_ver.minor, spec_ver.micro)
                cmp_func = _op_maps[id(specifier.op)]
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
    unsatisified_reasons: list[str]

    def __init__(self, reasons: list[str]):
        super().__init__()
        self.unsatisified_reasons = reasons


class PackageNameToZ3TupleVar(typing.Dict[PackageId, Z3Tuple]):
    def __missing__(self, key):
        v = self[key] = tuple_var(key)
        return v


def get_deps(mirror: str, meta: metadata) -> list[tuple[PackageId, version]]:
    name_to_z3_tuple: PackageNameToZ3TupleVar = PackageNameToZ3TupleVar()
    dep_graph: _DepGraph = typing.cast(_DepGraph, DefaultDict(lambda: DefaultDict(set)))
    solver = z3.Solver()
    requirements = list(
        update_deps_for_project(solver, dep_graph, name_to_z3_tuple, meta)
    )
    if solver.check() != z3.sat:
        raise DependencyUnsatisfied([uncomment(meta.name)])

    requirements_consumed = deque(requirements)
    reached: set[str] = set()

    while requirements_consumed:
        requirement = requirements_consumed.popleft()
        to_resolve = [requirement]
        while to_resolve:

            def comprehension():
                for pid in to_resolve:
                    if pid in reached:
                        continue
                    reached.add(pid)
                    yield request_pykg(mirror, pid)

            tasks = list(comprehension())
            to_resolve.clear()
            metas = run_many(tasks)
            to_resolve = []
            for meta_ in metas:
                if meta_ is None:
                    continue
                to_resolve.extend(
                    update_deps_for_project(solver, dep_graph, name_to_z3_tuple, meta_)
                )
        if solver.check() != z3.sat:
            raise DependencyUnsatisfied([uncomment(meta.name)])

    model = solver.model()
    print(model)

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

    ordered_packages = list(visit(uncomment(meta.name)))

    return [(pid, get_version_of_package(pid)) for pid in ordered_packages]
