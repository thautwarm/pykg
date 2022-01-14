import re
from _fable_pykg.src.comp import mk_version

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
    match_group = version_regex.match(extract_version).groupdict('0')
    major = int(match_group['major'])
    minor = int(match_group['minor'])
    micro = int(match_group['micro'])
    return mk_version(major, minor, micro)