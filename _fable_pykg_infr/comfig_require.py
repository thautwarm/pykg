from lark import Token
from decimal import Decimal
from _fable_pykg.src.comp import *


def lexeme(tk: Token):
    return str(tk)


def toArray(x):
    return x


def add(xs, x):
    xs.append(x)
    return xs


array = list
num = Decimal

try:
    toNum
except NameError:
    toNum = to_num


def one_or_list(x):
    if len(x) == 1:
        return x[0]
    return CList(x)
