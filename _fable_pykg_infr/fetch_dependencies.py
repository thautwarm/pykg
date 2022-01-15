from __future__ import annotations
from ast import And
from tkinter import Pack
from .async_request import (
    get_async_result,
    areadpage,
    run_many,
    gather_with_limited_workers,
)
from _fable_pykg.src.proj import parse_metadata, metadata
from _fable_pykg.src.comp import FromCompinentError, mk_version, operator, specifier, uncomment
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
    return z3.And(ge_tuple(y, x), lt_tuple(x, upper_bound))

def compact_compare(x: Z3Tuple, y: Z3Tuple):
    upper_bound = TupleCons(get_major(y) + 1, 0, 0)
    return z3.And(ge_tuple(y, x), lt_tuple(x, upper_bound))

_op_maps: typing.Dict[int, typing.Callable[[Z3Tuple, Z3Tuple], typing.Any]] = {
    id(comp.EQ) : eq_tuple,
    id(comp.NE): ne_tuple,
    id(comp.LT): lt_tuple,
    id(comp.LE): le_tuple,
    id(comp.GT): gt_tuple,
    id(comp.GE): ge_tuple,
    id(comp.COMPACT): compact_compare,
    id(comp.PATCH): patch_compare,
}

PackageId = str


def update_deps_for_project(
    deps: dict[PackageId, dict[version, dict[PackageId, set[specifier]]]],
    meta: metadata,
):
    pid = uncomment(meta.name)
    deps1 = deps[pid]
    assert meta.distributions.elements is not None
    for dist_ in meta.distributions.elements:
        dist = uncomment(dist_)
        deps2 = deps1[uncomment(dist.version)]
        assert dist.deps.elements is not None
        for each_dep_ in dist.deps.elements:
            each_dep = uncomment(each_dep_)
            dep_pid = each_dep.name
            dep3 = deps2[dep_pid]
            for specifier in uncomment(each_dep.version):
                dep3.add(specifier)
            yield dep_pid


if typing.TYPE_CHECKING:
    _DepGraph = typing.Dict[
        PackageId, typing.Dict[version, typing.Dict[PackageId, typing.Set[specifier]]]
    ]
else:
    _DepGraph = object

class DependencyUnsatisfied(Exception):
    unsatisified_reasons: list[str]

    def __init__(self, reasons: list[str]):
        super().__init__()
        self.unsatisified_reasons = reasons

def z3_tuple_to_version(x: Z3Tuple) -> version:
    major = z3.simplify(get_major(x)).as_long()  # type: ignore
    minor = z3.simplify(get_minor(x)).as_long()  # type: ignore
    micro = z3.simplify(get_micro(x)).as_long()  # type: ignore
    return mk_version(major, minor, micro)

def get_deps(mirror: str, package_name: PackageId) -> list[tuple[PackageId, version]]:
    to_resolve = [package_name]
    reached: dict[PackageId, Z3Tuple] = OrderedDict()
    dep_graph: _DepGraph = typing.cast(
        _DepGraph, DefaultDict(lambda: DefaultDict(lambda: DefaultDict(set)))
    )
    while to_resolve:

        def comprehension():
            for pid in to_resolve:
                if pid in reached:
                    continue
                reached[pid] = tuple_var(pid)
                yield request_pykg(mirror, pid)

        tasks = list(comprehension())
        to_resolve.clear()
        metas = run_many(tasks)
        to_resolve = []
        for meta in metas:
            if meta is None:
                continue
            to_resolve.extend(update_deps_for_project(dep_graph, meta))

    solver = z3.Solver()
    for pid, dists in dep_graph.items():
        z3_var_ver = reached[pid]
        for ver, dependencies in dists.items():
            cond = z3_var_ver == TupleCons(ver.major, ver.minor, ver.micro)
            solver.assert_and_track(cond, f"direct requirement {pid} {ver}")
            for dep_pid, dep_versions in dependencies.items():
                z3_var_dep_ver = reached[dep_pid]
                for each_spec in dep_versions:
                    spec_ver = each_spec.version
                    z3_spec_ver = TupleCons(spec_ver.major, spec_ver.minor, spec_ver.micro)
                    cmp_func = _op_maps[id(each_spec.op)]
                    solver.assert_and_track(
                        cmp_func(z3_var_dep_ver, z3_spec_ver),
                        f"{pid} depends on {dep_pid} >= {spec_ver}")

    if solver.check() != z3.sat:
        raise DependencyUnsatisfied([str(each) for each in solver.unsat_core()])

    model = solver.model()

    def really_reachable_step(source: PackageId, really_reached: dict[PackageId, version]):
        if source in really_reached:
            return []
        var_ver = reached[source]
        ver = z3_tuple_to_version(typing.cast(Z3Tuple, model[var_ver]))
        really_reached[source] = ver
        deps = dep_graph[source][ver]
        return list(deps.keys())

    reachable_to_solve = deque([package_name])
    really_reached : typing.Dict[PackageId, version] = typing.cast(typing.Dict[PackageId, version], OrderedDict())

    # must terminate as strictly monotonic and bound
    while reachable_to_solve:
        pid = reachable_to_solve.popleft()
        reachable_to_solve.extend(really_reachable_step(pid, really_reached))

    return list(really_reached.items())

