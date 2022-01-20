from __future__ import annotations
from dataclasses import dataclass
from distutils.ccompiler import gen_lib_options
from decimal import Decimal
from enum import Enum
from functools import lru_cache
from .version import Version
from . import log
from . import pretty_doc as doc
import typing
import copy
import json

if typing.TYPE_CHECKING:
    Component = typing.Union[
        "CNum",
        "CStr",
        "CBool",
        "CNull",
        "CCons",
        "CList",
        "CSpec",
        "CCommented",
        "CVer",
    ]

    def _cache(f):
        return f

else:
    _cache = lru_cache(maxsize=None)
    Component = object


@_cache
def normalize_name(x: str):
    assert isinstance(x, str)
    return x.lower().replace("_", "-")


class operator(Enum):
    EQ = 1
    NE = 2
    GT = 3
    LT = 4
    GE = 5
    LE = 6
    PATCH = 7
    COMPACT = 8

    def __str__(self):
        return operator_to_str_map[self]


EQ = operator.EQ
NE = operator.NE
GT = operator.GT
LT = operator.LT
GE = operator.GE
LE = operator.LE
PATCH = operator.PATCH
COMPACT = operator.COMPACT

operator_to_str_map = {
    EQ: "==",
    NE: "!=",
    GT: ">",
    LT: "<",
    GE: ">=",
    LE: "<=",
    PATCH: "~",
    COMPACT: "^",
}


@dataclass(frozen=True)
class specifier:
    op: operator
    version: Version

    def __str__(self) -> str:
        return f"{self.op} {self.version}"

@dataclass(frozen=True)
class CNum:
    v: Decimal


@dataclass(frozen=True)
class CStr:
    v: str


@dataclass(frozen=True)
class CBool:
    v: bool


@dataclass(frozen=True)
class CNull:
    pass


@dataclass(frozen=True)
class CCons:
    name: str
    param: Component


@dataclass(frozen=True)
class CList:
    elements: list[Component]


@dataclass(frozen=True)
class CSpec:
    specifier_set: SpecifierSet


@dataclass(frozen=True)
class CVer:
    ver: Version


@dataclass(frozen=True)
class CCommented:
    comments: list[str]
    value: Component


@dataclass
class TypeInfo:
    cls: type
    generics: typing.Tuple[TypeInfo, ...] | None
    construct: typing.Callable[[Component], object]  # Component -> 'a
    deconstruct: typing.Callable[[object], Component]  # 'a -> Component

    def __eq__(self, o):
        return self is o

    def __hash__(self):
        return object.__hash__(self)

    def show_name(self) -> str:
        if self.generics is None:
            return self.cls.__name__
        args = ", ".join(e.show_name() for e in self.generics)
        return f"{self.cls.__name__}[{args}]"

    def __repr__(self):
        return f"typeinfo<{self.show_name()}>"


UNSET = object()


class FromComponentError(Exception):
    pass


class Exc_FieldNotFound(Exception):
    pass


def unwrap_comment(x):
    if isinstance(x, CCommented):
        return x.value
    return x


def unwrap_field_tinfo(field_tinfo: TypeInfo):
    if field_tinfo.cls is None.__class__:
        assert field_tinfo.generics
        field_tinfo = field_tinfo.generics[0]

    if field_tinfo.cls is Commented:
        assert field_tinfo.generics
        field_tinfo = field_tinfo.generics[0]

    return field_tinfo


@dataclass(frozen=True)
class FieldInfo:
    typeinfo: TypeInfo
    name: str
    default: object = UNSET
    lift_array: bool = False
    recognize: typing.Callable[[Component], bool] | None = None

    def construct(self, xs: list[Component], used: list[bool]):
        if self.lift_array:
            res = []
            assert self.typeinfo.cls is list and self.typeinfo.generics
            field_info = self.typeinfo.generics[0]
            test_info = unwrap_field_tinfo(field_info)
            elt_typename = normalize_name(test_info.cls.__name__)
            for i, x in enumerate(xs):
                if used[i]:
                    continue
                x_test = unwrap_comment(x)
                if self.recognize and self.recognize(x_test):
                    used[i] = True
                    res.append(field_info.construct(x))
                elif (
                    isinstance(x_test, CCons)
                    and normalize_name(x_test.name) == elt_typename
                ):
                    used[i] = True
                    res.append(field_info.construct(x))

            return res

        for i, x in enumerate(xs):
            if used[i]:
                continue
            x_test = unwrap_comment(x)
            if self.recognize and self.recognize(x_test):
                used[i] = True
                return self.typeinfo.construct(x)
            elif isinstance(x_test, CCons) and x_test.name == normalize_name(self.name):
                used[i] = True
                if isinstance(x, CCommented):
                    self.typeinfo.construct(CCommented(x.comments, x_test.param))
                else:
                    return self.typeinfo.construct(x_test.param)

        if self.default is not UNSET:
            return copy.copy(self.default)

        raise Exc_FieldNotFound(self.name)

    def deconstruct(self, x):
        o = getattr(x, self.name)
        if self.lift_array:
            res = []
            assert self.typeinfo.cls is list and self.typeinfo.generics
            elt_info = self.typeinfo.generics[0]
            for x in o:
                res.append(elt_info.deconstruct(x))
            return res
        return [CCons(normalize_name(self.name), self.typeinfo.deconstruct(o))]


_T = typing.TypeVar("_T")


@dataclass
class Commented(typing.Generic[_T]):
    comments: list[str]
    uncomment: _T

    def __copy__(self):
        return Commented(self.comments.copy(), self.uncomment)

def cmt(x: _T) -> Commented[_T]:
    return Commented([], x)

def bool_construct(x: Component) -> bool:
    if isinstance(x, CBool):
        return bool(x.v)
    raise FromComponentError


def bool_deconstruct(x):
    return CNum(Decimal(x))


BoolType = TypeInfo(int, None, bool_construct, bool_deconstruct)


def int_construct(x: Component) -> int:
    if isinstance(x, CNum):
        return int(x.v)
    raise FromComponentError


def int_deconstruct(x):
    return CNum(Decimal(x))


IntType = TypeInfo(int, None, int_construct, int_deconstruct)


def float_construct(x: Component) -> float:
    if isinstance(x, CNum):
        return float(x.v)
    raise FromComponentError


def float_deconstruct(x):
    return CNum(Decimal(x))


FloatType = TypeInfo(float, None, float_construct, float_deconstruct)


def str_construct(x: Component) -> str:
    if isinstance(x, CStr):
        return x.v
    raise FromComponentError


def str_deconstruct(x):
    assert isinstance(x, str)
    return CStr(x)


StrType = TypeInfo(str, None, str_construct, str_deconstruct)


def spec_construct(x: Component) -> SpecifierSet:
    if isinstance(x, CSpec):
        return x.specifier_set
    raise FromComponentError


def spec_deconstruct(x):
    assert isinstance(x, SpecifierSet)
    return CSpec(x)


@dataclass
class SpecifierSet:
    specifiers: frozenset[specifier]

    def __str__(self) -> str:
        return '&&'.join(map(str, list(self.specifiers)))

    @staticmethod
    def singleton(spec: specifier):
        return SpecifierSet(frozenset([spec]))


SpecifierSetType = TypeInfo(SpecifierSet, None, spec_construct, spec_deconstruct)


def ver_construct(x: Component) -> Version:
    if isinstance(x, CVer):
        return x.ver
    raise FromComponentError(f"requires a version, got {x}")


def ver_deconstruct(x):
    return CVer(x)


VerType = TypeInfo(Version, None, ver_construct, ver_deconstruct)


@_cache
def list_type(tinfo: TypeInfo):
    def list_construct(x: Component):
        if isinstance(x, CList):
            res = []
            for each in x.elements:
                res.append(tinfo.construct(each))
            return res
        raise FromComponentError

    def list_deconstruct(xs):
        res = []
        for x in xs:
            res.append(tinfo.deconstruct(x))
        return CList(res)

    return TypeInfo(list, (tinfo,), list_construct, list_deconstruct)


@_cache
def commented_type(tinfo: TypeInfo):
    def cm_construct(x: Component):
        if isinstance(x, CCommented):
            v = tinfo.construct(x.value)
            return Commented(x.comments, v)
        else:
            v = tinfo.construct(x)
            return Commented([], v)
        raise FromComponentError

    def cm_deconstruct(xs: object) -> Component:
        assert isinstance(xs, Commented)
        comp = tinfo.deconstruct(xs.uncomment)
        return CCommented(xs.comments, comp)

    return TypeInfo(Commented, (tinfo,), cm_construct, cm_deconstruct)


@_cache
def tuple_type(*tinfos: TypeInfo):
    def tuple_construct(x: Component):
        if isinstance(x, CList) and len(x.elements) == len(tinfos):
            res = []
            for e, t in zip(x.elements, tinfos):
                res.append(t.construct(e))
            return tuple(res)
        raise FromComponentError

    def tuple_deconstruct(xs):
        assert len(xs) == len(tinfos)
        res = []
        for t, x in zip(tinfos, xs):
            res.append(t.deconstruct(x))
        return CList(res)

    return TypeInfo(tuple, tinfos, tuple_construct, tuple_deconstruct)


@_cache
def dataclass_type(
    cls: type,
    *field_makers: typing.Callable[[], FieldInfo],
    name_erased: typing.Callable[[], bool] | None = None,
):
    name = normalize_name(cls.__name__)

    def data_construct(x: Component):
        if name_erased and name_erased():
            if isinstance(x, CList):
                elements = x.elements
            else:
                elements = typing.cast("list[Component]", [x])
        elif isinstance(x, CCons) and normalize_name(x.name) == name:
            if isinstance(x.param, CList):
                elements = x.param.elements
            else:
                elements = typing.cast("list[Component]", [x.param])
        else:
            raise FromComponentError(f"parse {cls.__name__} from {x}")
        arguments = []
        used = [False] * len(elements)
        for field_maker in field_makers:
            fieldi = field_maker()
            arguments.append(fieldi.construct(elements, used))

        for i, is_used in enumerate(used):
            if not is_used:
                # TODO
                pass
        return cls(*arguments)

    def data_deconstruct(record):
        res = []

        for field_maker in field_makers:
            fieldi = field_maker()
            res.extend(fieldi.deconstruct(record))
        if name_erased and name_erased():
             return CList(res)
        return CCons(name, CList(res))

    return TypeInfo(cls, (), data_construct, data_deconstruct)


@_cache
def union_type(sealed_cls: type, get_cases: typing.Callable[[], tuple[TypeInfo, ...]]):
    def data_construct(x: Component):
        cases = get_cases()
        if not isinstance(x, CCons):
            raise FromComponentError
        for case in cases:
            casename = normalize_name(case.cls.__name__)
            if casename != normalize_name(x.name):
                continue
            return case.construct(x.param)
        raise FromComponentError

    def data_deconstruct(union):
        cases = get_cases()
        for case in cases:
            if isinstance(union, case.cls):
                casename = normalize_name(case.cls.__name__)
                return CCons(casename, case.deconstruct(union))
        raise FromComponentError

    return TypeInfo(sealed_cls, (), data_construct, data_deconstruct)


@_cache
def optional_type(tinfo: TypeInfo):
    def opt_construct(x: Component):
        if isinstance(x, CNull):
            return None

        return tinfo.construct(x)

    def opt_deconstruct(x):
        if x is None:
            return CNull()
        return tinfo.deconstruct(x)

    # XXX: we regard 'NoneType' as parameteric
    return TypeInfo(None.__class__, (tinfo,), opt_construct, opt_deconstruct)


def to_doc(c: Component) -> doc.Doc:
    if isinstance(c, CNull):
        return doc.seg("null")
    if isinstance(c, CNum):
        return doc.seg(str(c))
    if isinstance(c, CStr):
        return doc.seg(json.dumps(c.v, ensure_ascii=False))
    if isinstance(c, CSpec):
        return doc.seg(str(c.specifier_set))
    if isinstance(c, CBool):
        return doc.seg("true" if c.v else "false")
    if isinstance(c, CVer):
        return doc.seg(str(c.ver))
    if isinstance(c, CList):
        sep = doc.breakable(doc.space)
        return doc.vsep([
                doc.seg("{"),
                doc.indent(2,
                    doc.vsep(list(map(
                        to_doc,
                        c.elements)))),
                doc.seg("}")
            ])

    if isinstance(c, CCons):
        return doc.align(doc.seg(c.name) + to_doc(c.param))
    if isinstance(c, CCommented):
        return doc.vsep([
            *map(doc.seg, c.comments),
            to_doc(c.value)
        ])
    raise TypeError(c)
