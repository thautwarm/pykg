from __future__ import annotations
import re

version_regex = re.compile("\s*(?P<major>\d+)(\.(?P<minor>\d+)(\.(?P<micro>\d+))?)?\s*")


def parse_version(ver_string: str) -> tuple[int, int, int] | None:
    if res := version_regex.match(ver_string):
        x = res.groupdict(default=0)
        major = x["major"]
        minor = x["minor"]
        micro = x["micro"]
        return (int(major), int(minor), int(micro))
    return None


specifier_regex = re.compile(
    "\s*(?P<op>(\>\=|\>|\<\=|\<|\~\=|\!\=|\=\=\=|\=\=))\s*(?P<major>\d+)(\.(?P<minor>\d+)(\.(?P<micro>\d+))?)?\s*"
)


def parse_specifier(ver_string: str) -> tuple[str, tuple[int, int, int]] | None:
    if res := specifier_regex.match(ver_string):
        x = res.groupdict(default='0')
        op = x["op"]
        major = x["major"]
        minor = x["minor"]
        micro = x["micro"]
        return op, (int(major), int(minor), int(micro))
    return None
