from __future__ import annotations
from pykg import parser_wrap
from pykg.pretty_doc import RenderOptions
from .parse_typing import parse_typing
from .component import *
from dataclasses import is_dataclass
import typing
import sys
import copy

if typing.TYPE_CHECKING:

    def cache(x):
        return x


else:
    try:
        from functools import cache
    except ImportError:
        from functools import lru_cache

        cache = lru_cache(maxsize=None)

REFL_OPTS_FIELD = "__pykg_reflection_opts__"

REFL_IF_TYPENAME_ERASED_FIELD = "__pykg_reflection_typename_erased__"
REFL_FIELDINFO_FIELD = "__pykg_reflection__"

REFL_UNION_CASE_FIELD = "__pykg_union_cases__"


@dataclass
class ReflOpt:
    default: object = UNSET
    lift_to_array: bool | None = None
    recogniser: typing.Callable[[Component], bool] | None = None


def get_reflection_opts(cls) -> dict[str, ReflOpt]:
    if not is_dataclass(cls):
        raise TypeError(
            f"{get_reflection_opts.__name__} is not applicable to non-dataclass {cls}!"
        )
    if not hasattr(cls, REFL_OPTS_FIELD):
        opts = {
            fieldname: ReflOpt()
            for fieldname, _ in getattr(cls, "__annotations__", {}).items()
        }
        setattr(cls, REFL_OPTS_FIELD, opts)
    return getattr(cls, REFL_OPTS_FIELD)


def reflect_opt(
    fieldname: str,
    default: object = UNSET,
    lift_to_array: bool | None = None,
    recogniser=None,
):
    if typing.TYPE_CHECKING:

        def apply(x):
            return x

    else:

        def apply(cls: type):
            opt = get_reflection_opts(cls)[fieldname]
            if default is not UNSET:
                opt.default = copy.copy(default)
            if lift_to_array is not None:
                opt.lift_to_array = lift_to_array
            if recogniser is not None:
                opt.recogniser = recogniser
            return cls

    return apply


def erase_typename(cls):
    """
    Without '@allow_name_erasure',
    the following type parses "typename { x 1 }":

        # @allow_name_erasure
        @reflect
        @dataclass
        class TypeName:
            x: int

    After adding '@allow_name_erasure', it also
    parses '{ x 1 }'.

    """
    setattr(cls, REFL_IF_TYPENAME_ERASED_FIELD, True)
    return cls


def get_reflection_fieldinfo(
    cls: type, allow_exists=True
) -> list[typing.Callable[[], FieldInfo]]:
    if not is_dataclass(cls):
        raise TypeError(
            f"{get_reflection_fieldinfo.__name__} is not applicable to non-dataclass {cls}!"
        )
    refl = getattr(cls, REFL_FIELDINFO_FIELD, None)
    if refl is not None:
        if not allow_exists:
            raise TypeError(f"{cls} has already setup reflection.")
        return refl
    refl = []
    setattr(cls, REFL_FIELDINFO_FIELD, refl)
    return refl


def has_setup_reflection(cls: type):
    if not is_dataclass(cls):
        raise TypeError(
            f"{has_setup_reflection.__name__} is not applicable to non-dataclass {cls}!"
        )
    return hasattr(cls, REFL_FIELDINFO_FIELD)


REFL_REGISTRATION: dict[type, TypeInfo] = {
    int: IntType,
    float: FloatType,
    str: StrType,
    bool: BoolType,
    SpecifierSet: SpecifierSetType,
    Version: VerType,
}


def reflect_under(scope: dict):
    def apply(cls):
        return reflect(cls, scope)  # type: ignore

    return apply


def reflect_or(l: TypeInfo | None, r: TypeInfo | None):
    if l is None and isinstance(r, TypeInfo):
        return optional_type(r)
    elif r is None and isinstance(l, TypeInfo):
        return optional_type(l)

    raise TypeError(
        "'{l} | {r}' is not allowed in pykg datatype. only 'T | None' and 'None | T' is allowed."
    )


def _reflect(cls: type, scope: dict | None = None):
    """setup reflection for dataclasses"""
    if not is_dataclass(cls):
        raise TypeError(f"{reflect.__name__} is not applicable to non-dataclass {cls}!")

    if scope is None:
        scope = sys._getframe(1).f_globals

    if has_setup_reflection(cls):
        return cls

    refl = get_reflection_fieldinfo(cls)

    if hasattr(cls, "__annotations__"):
        for k, v in cls.__annotations__.items():
            if not isinstance(v, str):
                raise ValueError(
                    "you haven't done 'from __future__ import annotations' for such module!"
                )

            def capture(fieldname, type_annotation):
                @cache
                def get_tinfo():
                    opt = get_reflection_opts(cls)[fieldname]

                    tinfo = parse_typing(
                        type_annotation, scope, specialize, type_reflection, reflect_or,
                    )

                    if tinfo.cls is None.__class__ and opt.default is UNSET:
                        opt.default = None

                    if opt.lift_to_array and opt.default is UNSET:
                        opt.default = []

                    return FieldInfo(
                        tinfo,
                        fieldname,
                        default=opt.default,
                        lift_array=bool(opt.lift_to_array),
                        recognize=opt.recogniser,
                    )

                return get_tinfo

            refl.append(capture(k, v))

    def name_erased() -> bool:
        return hasattr(cls, REFL_IF_TYPENAME_ERASED_FIELD)

    REFL_REGISTRATION[cls] = dataclass_type(cls, *refl, name_erased=name_erased)
    return cls


if typing.TYPE_CHECKING:

    def reflect(cls):
        return cls


else:
    reflect = _reflect


def reflect_union(t):
    @classmethod
    def __init_subclass__(cls, *args, **kwargs):
        if hasattr(t, REFL_UNION_CASE_FIELD):
            cases_field = typing.cast("list | tuple", getattr(t, REFL_UNION_CASE_FIELD))
        else:
            cases_field = []
            setattr(t, REFL_UNION_CASE_FIELD, cases_field)
        if isinstance(cases_field, tuple):
            raise TypeError("cannot add new cases to sealed types!")
        cases_field.append(lambda: type_reflection(cls))

    def get_cases():
        if not hasattr(t, REFL_UNION_CASE_FIELD):
            return ()
        else:
            fields = getattr(t, REFL_UNION_CASE_FIELD)
            if isinstance(fields, list):
                fields = tuple(f() for f in fields)
                setattr(t, REFL_UNION_CASE_FIELD, fields)
            return fields

    t.__init_subclass__ = __init_subclass__
    REFL_REGISTRATION[t] = union_type(t, get_cases)
    return t


def type_reflection(t: type) -> TypeInfo:
    if tinfo := REFL_REGISTRATION.get(t):
        return tinfo
    raise TypeError(f"pykg reflection does not support {t}")


def specialize(cons, *targs: TypeInfo):
    if cons is typing.Callable:
        raise TypeError("pykg datatype does not support typing.Callable!")

    if cons in (dict, typing.Dict):
        raise TypeError("pykg datatype does not support typing.Dict!")

    if cons in (list, typing.List):
        if len(targs) != 1:
            raise TypeError("list takes 1 type argument!")

        return list_type(targs[0])

    if cons in (tuple, typing.Tuple):
        return tuple_type(*targs)

    if cons is typing.Optional:
        if len(targs) != 1:
            raise TypeError(f"{typing.Optional} takes 1 type argument!")
        return optional_type(targs[0])

    if cons is Commented:
        if len(targs) != 1:
            raise TypeError(f"{Commented} takes 1 type argument!")
        return commented_type(targs[0])

    raise TypeError(f"pykg datatype does not support reflection for {repr(cons)}.")


def to_comf(x, line_width: int | None = None):
    if line_width is None:
        opts = None
    else:
        opts = RenderOptions(line_width)
    return to_doc(type_reflection(type(x)).deconstruct(x)).show(opts)


_T = typing.TypeVar("_T")


def from_comf(t: typing.Type[_T], x: str) -> _T:
    comp = parser_wrap.parse(x)
    res = type_reflection(t).construct(comp)
    return typing.cast(_T, res)


__all__ = [
    "reflect",
    "reflect_opt",
    "type_reflection",
    "reflect_union",
    "get_reflection_opts",
    "erase_typename",
    "from_comf",
    "to_comf",
]

