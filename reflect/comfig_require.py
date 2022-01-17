from __future__ import annotations
from lark import Token
from decimal import Decimal
from .component import *
from .version import Version, mk_version
from io import StringIO

version = Version


def lexeme(tk: Token):
    return str(tk)


def toArray(x):
    return x


def add(xs, x):
    xs.append(x)
    return xs


array = list
num = Decimal

toNum = Decimal


def one_or_list(x):
    if len(x) == 1:
        return x[0]
    return CList(x)


def mk_specifier_set(xs: list[specifier]):
    return SpecifierSet(frozenset(xs))


mk_specifier = specifier


def parse_version(x: str):
    x = x[1:] # strip 'v'
    xs = x.split(".")
    return Version(*map(int, xs), *([0] * (3 - len(xs))))


def unesc(s: str) -> str:
    if True if (len(s) < 2) else (s[0] != '"'):
        raise Exception(f"invalid string literal {s}")

    buf = StringIO()
    find_end: bool = False
    i: int = 1
    while not find_end if (i < len(s)) else (False):
        match_value: str = s[i]
        if match_value == '"':
            find_end = True
            i = (i + 1) or 0

        elif match_value == "\\":
            if (i + 1) >= len(s):
                raise Exception("incomplete escape for string")

            else:
                match_value_1: str = s[i + 1]
                if match_value_1 == "b":
                    buf.write("\b")

                elif match_value_1 == "f":
                    buf.write("\f")

                elif match_value_1 == "n":
                    buf.write("\n")

                elif match_value_1 == "r":
                    buf.write("\r")

                elif match_value_1 == "t":
                    buf.write("\t")

                else:
                    buf.write(match_value_1)

                i = (i + 2) or 0

        else:
            buf.write(match_value)
            i = (i + 1) or 0

    if find_end:
        return buf.getvalue()

    else:
        raise Exception("string literal not closed")


def sink_comments(xs: list[Component]):
    res = []
    for each in xs:
        if isinstance(each, CCommented) and isinstance(each.value, CCons):
            res.append(
                CCons(each.value.name, CCommented(each.comments, each.value.param)))
        else:
            res.append(each)
    return res
