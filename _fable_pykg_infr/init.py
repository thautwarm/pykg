from _fable_pykg.src.comp import read_file
from .comfig_parser import parser


def _read_file(x: str):
    with open(x, encoding="utf8") as f:
        return f.read()


read_file.contents = _read_file


def parse(s: str):
    return parser.parse(s)


__all__ = ["parse"]
