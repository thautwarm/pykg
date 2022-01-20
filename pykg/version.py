import re
from dataclasses import dataclass

@dataclass(frozen=True, order=True)
class Version:
    major: int
    minor: int
    micro: int

    def __str__(self):
        return f"v{self.major}.{self.minor}.{self.micro}"
    
    def to_string_without_prefix(self):
        return f"{self.major}.{self.minor}.{self.micro}"


def mk_version(a: int, b: int, c: int) -> Version:
    return Version(a, b, c)


version_regex_wildcard = re.compile(
    "^\s*v?(?P<major>\d+)(\.(?P<minor>\d+|\*)(\.(?P<micro>\d+|\*))?)?\s*$"
)
version_regex = re.compile(
    "^\s*v?(?P<major>\d+)(\.(?P<minor>\d+)(\.(?P<micro>\d+))?)?\s*$"
)
version_regex_incomplete = re.compile(
    "^\s*v?(?P<major>\d+)(\.(?P<minor>\d+)(\.(?P<micro>\d+))?)?"
)


def get_typed_version(extract_version: str):
    match_group = version_regex.match(extract_version)
    assert match_group
    match_group = match_group.groupdict("0")
    major = int(match_group["major"])
    minor = int(match_group["minor"])
    micro = int(match_group["micro"])
    return mk_version(major, minor, micro)
