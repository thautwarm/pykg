from __future__ import annotations
from io import StringIO
from pathlib import Path
from string import ascii_letters, digits

from pykg.version import Version
_ascii_alphabeta = frozenset(ascii_letters + digits)

def to_posix(x: str | Path):
    if isinstance(x, Path):
        return x.as_posix()

    return Path(x).as_posix()

def to_netversion(x: Version):
    return f"net{x.major}.{x.minor}.{x.micro}"

def to_valid_identifier(x: str, ignore_dash=False):
    buf = StringIO()
    for c in x:
        if c in _ascii_alphabeta:
            buf.write(c)
        elif c == '-':
            if ignore_dash:
                buf.write('_')
            else:
                buf.write('__m' + str(ord(c)))
        else:
            buf.write('__m' + str(ord(c)))
    return buf.getvalue()
