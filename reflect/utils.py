from __future__ import annotations
from io import StringIO
from pathlib import Path
from string import ascii_letters

from reflect.version import Version
_ascii_letters = frozenset(ascii_letters)

def to_posix(x: str | Path):
    if isinstance(x, Path):
        return x.as_posix()

    return Path(x).as_posix()

def to_netversion(x: Version):
    return f"net{x.major}.{x.minor}.{x.micro}"
     
def to_valid_identifier(x: str):
    buf = StringIO()
    for c in x:
        if c in _ascii_letters:
            buf.write(c)
        elif c == '_':
            buf.write('__')
        else:
            buf.write('_' + str(ord(c)))
    return buf.getvalue()
    