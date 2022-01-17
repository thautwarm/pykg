from http.client import responses
from os import sep
from struct import pack
from bs4 import BeautifulSoup
from .async_request import (
    get_async_result,
    areadpage,
    run_many,
    gather_with_limited_workers,
)
from .component import specifier as mk_specifier
from .component import operator as comp
from types import GeneratorType
from packaging.requirements import Requirement
from . import log
from .version import *
import json
import re


def request_pypi_package_versions(package_name: str):
    resp, v = yield from areadpage(rf"https://pypi.org/simple/{package_name}/")
    if resp.status != 200:
        return []
    results = []
    found = set()
    for each in BeautifulSoup(v, features="html.parser").findAll(name="a"):
        name = each.text
        name = name[len(package_name) + 1 :]
        if m := version_regex_incomplete.match(name):
            pass
        else:
            continue
        a1, a2 = m.span()
        version = name[a1:a2].strip()
        if version in found:
            continue
        results.append(version)
    results.reverse()
    return results


def request_pypi_package_with_version(package_name: str, version: str):
    resp, v = yield from areadpage(rf"https://pypi.org/pypi/{package_name}/{version}/json")
    if resp.status != 200:
        raise ConnectionError
    return v

# https://www.python.org/dev/peps/pep-0508/
# '~=', '!=' and '==' are specially handled
_op_maps = {"<": comp.LT, "<=": comp.LE, ">": comp.GT, ">=": comp.GE, "===": comp.EQ}


def require_python_package_deps_for_version(package_name: str, ver: str):
    try:
        data = yield from request_pypi_package_with_version(package_name, ver)
    except ConnectionError:  #  not JSON: '\r\n\r\n' not found
        log.warn(f"{package_name} {ver}: invalid connection; skipping it...")
        return None

    try:
        pack_info = json.loads(data)
    except json.JSONDecodeError:
        log.warn(f"{package_name} {ver}: invalid JSON data; skipping it...")
        return None
    try:
        requires_dist = pack_info["info"].get("requires_dist", [])
        if not isinstance(requires_dist, list):
            log.warn(
                f"{package_name} {ver}: invalid JSON fields; skipping it..."
            )
            return None
    except ValueError:
        log.warn(f"{package_name} {ver}: invalid JSON; skipping it...")
        return None

    results = []

    for each in map(Requirement, requires_dist):
        dep_pack_name = each.name
        specifiers = []
        yield
        for spec in list(each.specifier):
            if spec.operator == "==":
                if m := version_regex_wildcard.match(spec.version):
                    pass
                else:
                    log.warn(
                        f"{dep_pack_name}: {spec} is not a dependency specifier; skipping it..."
                    )
                    continue
                match_group = m.groupdict("*")
                major = int(match_group["major"])
                if match_group["minor"] == "*":
                    specifiers.extend(
                        [
                            mk_specifier(comp.GE, mk_version(major, 0, 0)),
                            mk_specifier(comp.LT, mk_version(major + 1, 0, 0)),
                        ]
                    )
                    continue
                minor = int(match_group["minor"])
                if match_group["micro"] == "*":
                    specifiers.extend(
                        [
                            mk_specifier(comp.GE, mk_version(major, minor, 0)),
                            mk_specifier(comp.LT, mk_version(major, minor + 1, 0)),
                        ]
                    )
                    continue
                micro = int(match_group["micro"])
                specifiers.append(
                    mk_specifier(comp.EQ, mk_version(major, minor, micro))
                )
                break
            elif spec.operator == "!=":
                if m := version_regex_wildcard.match(spec.version):
                    pass
                else:
                    log.warn(
                        f"{dep_pack_name}: {spec} is not a dependency specifier; skipping it..."
                    )
                    continue
                match_group = m.groupdict("*")
                major = int(match_group["major"])
                if match_group["minor"] == "*":
                    specifiers.extend(
                        [
                            mk_specifier(comp.LT, mk_version(major, 0, 0)),
                            mk_specifier(comp.GE, mk_version(major + 1, 0, 0)),
                        ]
                    )
                    continue
                minor = int(match_group["minor"])
                if match_group["micro"] == "*":
                    specifiers.extend(
                        [
                            mk_specifier(comp.LT, mk_version(major, minor, 0)),
                            mk_specifier(comp.GE, mk_version(major, minor + 1, 0)),
                        ]
                    )
                    continue
                micro = int(match_group["micro"])
                specifiers.append(
                    mk_specifier(comp.NE, mk_version(major, minor, micro))
                )
                continue
            elif spec.operator == "~=":
                if m := version_regex.match(spec.version):
                    pass
                else:
                    log.warn(
                        f"{dep_pack_name}: {spec} is not a dependency specifier; skipping it..."
                    )
                    continue
                match_group = m.groupdict(None)  # type: ignore
                major = int(match_group["major"])  # type: ignore
                if match_group["minor"] is None:
                    specifiers.append(
                        mk_specifier(comp.GE, mk_version(major, 0, 0))
                    )
                    continue
                minor = int(match_group["minor"])
                if match_group["micro"] is None:
                    specifiers.extend(
                        [
                            mk_specifier(comp.GE, mk_version(major, minor, 0)),
                            mk_specifier(comp.LT, mk_version(major + 1, 0, 0)),
                        ]
                    )
                    continue
                micro = int(match_group["micro"])
                specifiers.extend(
                    [
                        mk_specifier(comp.GE, mk_version(major, minor, micro)),
                        mk_specifier(comp.LT, mk_version(major, minor + 1, 0)),
                    ]
                )
            else:
                if m := version_regex.match(spec.version):
                    pass
                else:
                    log.warn(
                        f"{dep_pack_name}: {spec} is not a dependency specifier; skipping it..."
                    )
                    continue
                match_group = m.groupdict("0")
                major = int(match_group["major"])
                minor = int(match_group["minor"])
                micro = int(match_group["micro"])
                specifiers.append(
                    mk_specifier(
                        _op_maps[spec.operator], mk_version(major, minor, micro)
                    )
                )

        results.append((dep_pack_name, specifiers))

    return package_name, results


def require_python_package_versions_and_deps(
    package_name: str, sync: bool = False, nworkers: int = 16
):
    try:
        versions = yield from request_pypi_package_versions(package_name)
    except ValueError:
        raise ConnectionError("the PyPI server returned incorrect results; you might decrease the number of green threads.")


    if sync:
        results = []
        for ver in versions:
            package = yield from require_python_package_deps_for_version(package_name, ver)
            if package is None:
                continue
            results.append((ver, package))
        return results
    else:
        packages = yield from gather_with_limited_workers(
            [require_python_package_deps_for_version(package_name, ver) for ver in versions],
            nworkers=nworkers
        )
        return [(ver, package) for ver, package in zip(versions, packages) if package is not None]


__all__ = [
    "require_python_package_versions_and_deps",
]
