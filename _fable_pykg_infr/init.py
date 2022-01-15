from _fable_pykg.src.comp import read_file
from .comfig_parser import parser
from .errors import InvalidComfigVersion


def _read_file(x: str):
    with open(x, encoding="utf8") as f:
        return f.read()


read_file.contents = _read_file


def parse(s: str):
    ver, comp = parser.parse(s)
    if ver.major == 0 and ver.minor == 1:
       pass
    else:
        raise InvalidComfigVersion(f"expect version v0.1.*, got {ver}")
    return comp


__all__ = ["parse"]
