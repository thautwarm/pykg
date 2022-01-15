from __future__ import annotations
from _fable_pykg_infr import Version
from typing import (Any, List, TypeVar, Generic, Tuple, Optional, Callable, MutableSequence)
from ..fable_modules.fable_library.array import (equals_with, pick, try_pick, iterate_indexed, fill, try_find_index, map, initialize, try_find, map_indexed)
from ..fable_modules.fable_library.choice import FSharpChoice_2
from ..fable_modules.fable_library.decimal import (Decimal, to_number, to_number as to_number_1, to_string as to_string_1)
from ..fable_modules.fable_library.int32 import parse
from ..fable_modules.fable_library.list import (of_array, empty, FSharpList, cons, to_array, map as map_1)
from ..fable_modules.fable_library.long import (from_number, to_number as to_number_2)
from ..fable_modules.fable_library.option import (value as value_31, some)
from ..fable_modules.fable_library.reflection import (TypeInfo, class_type, union_type, array_type, record_type, string_type, bool_type, option_type, lambda_type, is_generic_type, equals as equals_1, get_generic_type_definition, obj_type, get_generics, name, int8_type, int16_type, int32_type, float64_type, char_type, unit_type, is_array, uint32_type, uint8_type, uint16_type, list_type, is_record, get_record_elements, make_record, is_tuple, get_tuple_elements, make_tuple, is_union, get_union_cases, get_union_case_fields, make_union, get_element_type, get_record_field, get_tuple_fields, get_union_fields)
from ..fable_modules.fable_library.seq import (to_array as to_array_1, delay, collect, map as map_2, singleton, append, empty as empty_1)
from ..fable_modules.fable_library.string import (to_text, interpolate, split)
from ..fable_modules.fable_library.system_text import (StringBuilder__ctor, StringBuilder__Append_244C7CD6, StringBuilder__ctor_Z524259A4, StringBuilder__Append_Z721C83C5)
from ..fable_modules.fable_library.types import (FSharpException, Union, Record, to_string, FSharpRef, Int32Array, Int16Array, Int8Array, Uint32Array, Uint8Array, Uint16Array, Float64Array)
from ..fable_modules.fable_library.util import (equals, ignore, get_enumerator, dispose, IEnumerable)
from .pretty_doc import (seg, Doc, separray, vsep, Doc_op_Multiply_Z32C4A9C0, align, indent, Doc_op_Addition_Z32C4A9C0)

_A = TypeVar("_A")

__A = TypeVar("__A")

__B = TypeVar("__B")

_B = TypeVar("_B")

AllowOmit_Name : str = "name"

AllowOmit_Version : str = "version"

AllowUnused_Field : str = "_unused"

def expr_82() -> TypeInfo:
    return class_type("FablePykg.Comp.ParseComponentError", None, ParseComponentError, class_type("System.Exception"))


class ParseComponentError(FSharpException):
    def __init__(self, Data0: str) -> None:
        super().__init__()
        self.Data0 = Data0
    

ParseComponentError_reflection = expr_82

def ParseComponentError__Equals_229D3F39(this: Exception, obj: Exception) -> bool:
    if not equals(this, None):
        if not equals(obj, None):
            if isinstance(obj, ParseComponentError):
                return this.Data0 == obj.Data0
            
            else: 
                return False
            
        
        else: 
            return False
        
    
    elif not equals(obj, None):
        return False
    
    else: 
        return True
    


def expr_83() -> TypeInfo:
    return class_type("FablePykg.Comp.FromCompinentError", None, FromCompinentError, class_type("System.Exception"))


class FromCompinentError(FSharpException):
    def __init__(self, Data0: str) -> None:
        super().__init__()
        self.Data0 = Data0
    

FromCompinentError_reflection = expr_83

def FromCompinentError__Equals_229D3F39(this: Exception, obj: Exception) -> bool:
    if not equals(this, None):
        if not equals(obj, None):
            if isinstance(obj, FromCompinentError):
                return this.Data0 == obj.Data0
            
            else: 
                return False
            
        
        else: 
            return False
        
    
    elif not equals(obj, None):
        return False
    
    else: 
        return True
    


def expr_84() -> TypeInfo:
    return class_type("FablePykg.Comp.ToComponentError", None, ToComponentError, class_type("System.Exception"))


class ToComponentError(FSharpException):
    def __init__(self, Data0: str) -> None:
        super().__init__()
        self.Data0 = Data0
    

ToComponentError_reflection = expr_84

def ToComponentError__Equals_229D3F39(this: Exception, obj: Exception) -> bool:
    if not equals(this, None):
        if not equals(obj, None):
            if isinstance(obj, ToComponentError):
                return this.Data0 == obj.Data0
            
            else: 
                return False
            
        
        else: 
            return False
        
    
    elif not equals(obj, None):
        return False
    
    else: 
        return True
    


def expr_85() -> TypeInfo:
    return union_type("FablePykg.Comp.operator", [], operator, lambda: [[], [], [], [], [], [], [], []])


class operator(Union):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["EQ", "NE", "GT", "GE", "LT", "LE", "COMPACT", "PATCH"]
    

operator_reflection = expr_85

def operator__get_Show(this: operator) -> str:
    if this.tag == 1:
        return "!="
    
    elif this.tag == 2:
        return "\u003e"
    
    elif this.tag == 3:
        return "\u003e="
    
    elif this.tag == 4:
        return "\u003c"
    
    elif this.tag == 5:
        return "\u003c="
    
    elif this.tag == 6:
        return "^"
    
    elif this.tag == 7:
        return "~"
    
    else: 
        return "=="
    


EQ : operator = operator(0)

NE : operator = operator(1)

GT : operator = operator(2)

GE : operator = operator(3)

LT : operator = operator(4)

LE : operator = operator(5)

COMPACT : operator = operator(6)

PATCH : operator = operator(7)

def expr_86(gen0: TypeInfo) -> TypeInfo:
    return record_type("FablePykg.Comp.lift_array`1", [gen0], lift_array_1, lambda: [["elements", array_type(gen0)]])


class lift_array_1(Record, Generic[_A]):
    def __init__(self, elements: List[_A]=None) -> None:
        super().__init__()
        self.elements = elements
    

lift_array_1_reflection = expr_86

def create_lift_array(x: List[_A]) -> lift_array_1[_A]:
    return lift_array_1(x)


def expr_87(gen0: TypeInfo) -> TypeInfo:
    return union_type("FablePykg.Comp.commented`1", [gen0], commented_1, lambda: [[["comments", array_type(string_type)], ["value", gen0]]])


class commented_1(Union, Generic[_A]):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["Commented"]
    

commented_1_reflection = expr_87

def commented_1__get_uncomment(self_1: commented_1[_A]) -> _A:
    return self_1.fields[1]


def uncomment(a: commented_1[__A]) -> __A:
    return commented_1__get_uncomment(a)


def mk_version(major: int, minor: int, micro: int) -> Version:
    return Version(major, minor, micro)


def expr_88() -> TypeInfo:
    return record_type("FablePykg.Comp.specifier", [], specifier, lambda: [["op", operator_reflection()], ["version", class_type("FablePykg.Comp.version")]])


class specifier(Record):
    def __init__(self, op: operator, version: Version) -> None:
        super().__init__()
        self.op = op
        self.version = version
    
    def __str__(self) -> str:
        this : specifier = self
        return specifier__get_Show(this)
    

specifier_reflection = expr_88

def specifier__get_Show(spec: specifier) -> str:
    return to_text(interpolate("%P() %P()", [operator__get_Show(spec.op), spec.version]))


def mk_specifier(op: operator, v: Version) -> specifier:
    return specifier(op, v)


def expr_89() -> TypeInfo:
    return union_type("FablePykg.Comp.Component", [], Component, lambda: [[], [["Item", class_type("System.Decimal")]], [["Item", string_type]], [["Item", bool_type]], [["Item1", string_type], ["Item2", array_type(Component_reflection())]], [["elements", array_type(Component_reflection())]], [["Item", class_type("FablePykg.Comp.version")]], [["Item", array_type(specifier_reflection())]], [["comments", array_type(string_type)], ["Item2", Component_reflection()]]])


class Component(Union):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["CNull", "CNum", "CStr", "CBool", "CCons", "CList", "CVer", "CSpec", "CCommented"]
    

Component_reflection = expr_89

def Component__get_kind(this: Component) -> str:
    if this.tag == 2:
        return "string"
    
    elif this.tag == 3:
        return "bool"
    
    elif this.tag == 4:
        return to_text(interpolate("constructor %P()", [this.fields[0]]))
    
    elif this.tag == 5:
        return "list"
    
    elif this.tag == 6:
        return "version"
    
    elif this.tag == 8:
        return to_text(interpolate("%P() with comments", [Component__get_kind(this.fields[1])]))
    
    elif this.tag == 0:
        return "null"
    
    elif this.tag == 7:
        return "specifiers"
    
    else: 
        return "number"
    


def unesc(s: str) -> str:
    if True if (len(s) < 2) else (s[0] != "\""):
        raise Exception(to_text(interpolate("invalid string literal %P()", [s])))
    
    else: 
        buf : Any = StringBuilder__ctor()
        find_end : bool = False
        i : int = 1
        while not find_end if (i < len(s)) else (False):
            match_value : str = s[i]
            if match_value == "\"":
                find_end = True
                i = (i + 1) or 0
            
            elif match_value == "\\":
                if (i + 1) >= len(s):
                    raise Exception("incomplete escape for string")
                
                else: 
                    match_value_1 : str = s[i + 1]
                    if match_value_1 == "b":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\b"))
                    
                    elif match_value_1 == "f":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\f"))
                    
                    elif match_value_1 == "n":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\n"))
                    
                    elif match_value_1 == "r":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\r"))
                    
                    elif match_value_1 == "t":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\t"))
                    
                    else: 
                        ignore(StringBuilder__Append_244C7CD6(buf, match_value_1))
                    
                    i = (i + 2) or 0
                
            
            else: 
                ignore(StringBuilder__Append_244C7CD6(buf, match_value))
                i = (i + 1) or 0
            
        if find_end:
            return to_string(buf)
        
        else: 
            raise Exception("string literal not closed")
        
    


def escape_string(s: str) -> str:
    buf : Any = StringBuilder__ctor_Z524259A4(len(s))
    for i in range(0, (len(s) - 1) + 1, 1):
        def arrow_90(s: str=s) -> Any:
            c : str = s[i]
            return StringBuilder__Append_Z721C83C5(buf, "\\b") if (c == "\b") else (StringBuilder__Append_Z721C83C5(buf, "\\t") if (c == "\t") else (StringBuilder__Append_Z721C83C5(buf, "\\n") if (c == "\n") else (StringBuilder__Append_Z721C83C5(buf, "\\f") if (c == "\f") else (StringBuilder__Append_Z721C83C5(buf, "\\r") if (c == "\r") else (StringBuilder__Append_Z721C83C5(buf, "\\\"") if (c == "\"") else (StringBuilder__Append_Z721C83C5(buf, "\\\\") if (c == "\\") else (StringBuilder__Append_244C7CD6(buf, c))))))))
        
        ignore(arrow_90())
    return to_string(buf)


def CNum(d: Any) -> Component:
    return Component(1, d)


def CStr(d: str) -> Component:
    return Component(2, d)


def CBool(d: bool) -> Component:
    return Component(3, d)


def CCons(d_0: str, d_1: List[Component]) -> Component:
    tupled_arg : Tuple[str, List[Component]] = (d_0, d_1)
    return Component(4, tupled_arg[0], tupled_arg[1])


def CCommented(a: List[str], b: Component) -> Component:
    return Component(8, a, b)


def CList(d: List[Component]) -> Component:
    return Component(5, d)


def parse_version(s: str) -> Version:
    s_1 : str = s[1:(len(s) - 1) + 1]
    match_value : List[str] = split(s_1, ["."], None, 0)
    def arrow_91(x: str, y: str, s: str=s) -> bool:
        return x == y
    
    if len(match_value) == 1 if (not equals_with(arrow_91, match_value, None)) else (False):
        return mk_version(parse(match_value[0], 511, False, 32), 0, 0)
    
    else: 
        def arrow_92(x_1: str, y_1: str, s: str=s) -> bool:
            return x_1 == y_1
        
        if len(match_value) == 2 if (not equals_with(arrow_92, match_value, None)) else (False):
            minor : str = match_value[1]
            return mk_version(parse(match_value[0], 511, False, 32), parse(minor, 511, False, 32), 0)
        
        else: 
            def arrow_93(x_2: str, y_2: str, s: str=s) -> bool:
                return x_2 == y_2
            
            if len(match_value) == 3 if (not equals_with(arrow_93, match_value, None)) else (False):
                minor_1 : str = match_value[1]
                micro : str = match_value[2]
                return mk_version(parse(match_value[0], 511, False, 32), parse(minor_1, 511, False, 32), parse(micro, 511, False, 32))
            
            else: 
                raise Exception(to_text(interpolate("impossible version string %P()", [s_1])))
            
        
    


CNull : Component = Component(0)

def CVer(a: Version) -> Component:
    return Component(6, a)


def CSpec(a: List[specifier]) -> Component:
    return Component(7, a)


def toNum(x: str) -> Any:
    return Decimal(x)


def _007CCase_007C__007C(s: str, v: Component) -> Optional[List[Component]]:
    (pattern_matching_result, args_1, f_1) = (None, None, None)
    if v.tag == 4:
        if s == v.fields[0]:
            pattern_matching_result = 0
            args_1 = v.fields[1]
            f_1 = v.fields[0]
        
        else: 
            pattern_matching_result = 1
        
    
    else: 
        pattern_matching_result = 1
    
    if pattern_matching_result == 0:
        return args_1
    
    elif pattern_matching_result == 1:
        return None
    


def expr_94(gen0: TypeInfo) -> TypeInfo:
    return record_type("FablePykg.Comp.Picker`1", [gen0], Picker_1, lambda: [["require", string_type], ["picker", lambda_type(Component_reflection(), option_type(gen0))]])


class Picker_1(Record, Generic[_A]):
    def __init__(self, require: str, picker: Callable[[Component], Optional[_A]]) -> None:
        super().__init__()
        self.require = require
        self.picker = picker
    

Picker_1_reflection = expr_94

def Array_pickOne() -> Callable[[Callable[[__A], Optional[__B]], List[__A]], __B]:
    def arrow_96(chooser: Callable[[__A], Optional[__B]]) -> Callable[[List[__A]], __B]:
        def arrow_95(array: List[__A]) -> Any:
            return pick(chooser, array)
        
        return arrow_95
    
    return arrow_96


def Array_tryPickOne() -> Callable[[Callable[[__A], Optional[__B]], List[__A]], Optional[__B]]:
    def arrow_98(chooser: Callable[[__A], Optional[__B]]) -> Callable[[List[__A]], Optional[__B]]:
        def arrow_97(array: List[__A]) -> Optional[__B]:
            return try_pick(chooser, array)
        
        return arrow_97
    
    return arrow_98


def Array_pickAll(f: Callable[[_A], Optional[_B]], xs: List[_A]) -> List[_B]:
    res : List[_B] = []
    for idx in range(0, (len(xs) - 1) + 1, 1):
        match_value : Optional[_B] = f(xs[idx])
        if match_value is not None:
            v : _B = value_31(match_value)
            (res.append(v))
        
    return res.slice()


def Array_tryFindIndices(f: Callable[[_A], bool], xs: List[_A]) -> MutableSequence[int]:
    res : MutableSequence[int] = []
    def action(i: int, x: Any=None, f: Callable[[_A], bool]=f, xs: List[_A]=xs) -> None:
        if f(x):
            ignore((res.append(i)))
        
    
    iterate_indexed(action, xs)
    return res


def _007CFind_007C(f: Callable[[__A], Optional[__B]], v: List[__A]) -> __B:
    return pick(f, v)


def _007CFindAll_007C(f: Callable[[__A], Optional[__B]], v: List[__A]) -> List[__B]:
    return Array_pickAll(f, v)


def _007CTryFind_007C(f: Callable[[__A], Optional[__B]], v: List[__A]) -> Optional[__B]:
    return try_pick(f, v)


read_file : FSharpRef[Callable[[str], str]] = FSharpRef(None)

def num_from_comp(_arg1: Component) -> Any:
    if _arg1.tag == 1:
        return _arg1.fields[0]
    
    else: 
        raise FromCompinentError("invalid conversion to int")
    


def bool_from_comp(_arg1: Component) -> bool:
    if _arg1.tag == 3:
        return _arg1.fields[0]
    
    else: 
        raise FromCompinentError("invalid conversion to bool")
    


def string_from_comp(_arg1: Component) -> str:
    if _arg1.tag == 2:
        return _arg1.fields[0]
    
    else: 
        raise FromCompinentError("invalid conversion to bool")
    


def char_from_comp(data: Component) -> str:
    s : str = string_from_comp(data)
    if len(s) != 1:
        raise FromCompinentError(to_text(interpolate("%P() to char", [s])))
    
    else: 
        return s[0]
    


def is_option_type(t: Any) -> bool:
    if is_generic_type(t):
        return equals_1(get_generic_type_definition(t), option_type(obj_type))
    
    else: 
        return False
    


def expr_99(gen0: TypeInfo) -> TypeInfo:
    return union_type("FablePykg.Comp.evidence`1", [gen0], evidence_1, lambda: [[]])


class evidence_1(Union, Generic[_A]):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["Evidence"]
    

evidence_1_reflection = expr_99

def _007CNotCList_007CIsCList_007C(x: Component) -> Any:
    if x.tag == 5:
        return FSharpChoice_2(1, x.fields[0])
    
    else: 
        return FSharpChoice_2(0, None)
    


def real_type_name(t_mut: Any) -> str:
    while True:
        (t,) = (t_mut,)
        def arrow_100(t: Any=t) -> bool:
            t_1 : Any = t
            return equals_1(get_generic_type_definition(t_1), commented_1_reflection(obj_type)) if (is_generic_type(t_1)) else (False)
        
        if arrow_100():
            t_mut = get_generics(t)[0]
            continue
        
        else: 
            return name(t)
        
        break


def extract_field_arguments(tname: str, finfo: List[Any], elements: List[Component]) -> List[Any]:
    arguments : List[Any] = fill([0] * len(finfo), 0, len(finfo), None)
    def predicate(f: Any, tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> bool:
        if name(f) == AllowUnused_Field:
            return equals_1(array_type(Component_reflection()), f[1])
        
        else: 
            return False
        
    
    unused_field : Optional[int] = try_find_index(predicate, finfo)
    def f_2(f_1: Any, tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> bool:
        t : Any = f_1[1]
        if is_generic_type(t):
            return equals_1(get_generic_type_definition(t), lift_array_1_reflection(obj_type))
        
        else: 
            return False
        
    
    lifted_fields : MutableSequence[int] = Array_tryFindIndices(f_2, finfo)
    enumerator : Any = get_enumerator(lifted_fields)
    try: 
        while enumerator.System_Collections_IEnumerator_MoveNext():
            i : int = enumerator.System_Collections_Generic_IEnumerator_00601_get_Current() or 0
            arguments[i] = create_lift_array([])
    
    finally: 
        dispose(enumerator)
    
    def mapping(f_3: Any, tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> Tuple[str, Any]:
        def arrow_101(f_3: Any=f_3) -> bool:
            t_1 : Any = f_3[1]
            return equals_1(get_generic_type_definition(t_1), lift_array_1_reflection(obj_type)) if (is_generic_type(t_1)) else (False)
        
        if arrow_101():
            inner_t : Any = get_generics(f_3[1])[0]
            return (real_type_name(inner_t), inner_t)
        
        else: 
            return (name(f_3), f_3[1])
        
    
    finfo_1 : List[Tuple[str, Any]] = map(mapping, finfo, None)
    if unused_field is not None:
        i_1 : int = unused_field or 0
        arguments[i_1] = []
    
    for idx in range(0, (len(elements) - 1) + 1, 1):
        each : Component = elements[idx]
        i_2 : int = 0
        break_0027 : bool = False
        while i_2 < len(finfo_1) if (not break_0027) else (False):
            pattern_input : Tuple[str, Any] = finfo_1[i_2]
            ftype : Any = pattern_input[1]
            fname : str = pattern_input[0]
            is_lifted : bool = i_2 in lifted_fields
            (pattern_matching_result,) = (None,)
            if each.tag == 4:
                if each.fields[0] == fname if (is_lifted) else (False):
                    pattern_matching_result = 0
                
                else: 
                    pattern_matching_result = 1
                
            
            elif each.tag == 8:
                if each.fields[1].tag == 4:
                    if each.fields[1].fields[0] == fname if (is_lifted) else (False):
                        pattern_matching_result = 0
                    
                    else: 
                        pattern_matching_result = 1
                    
                
                else: 
                    pattern_matching_result = 1
                
            
            else: 
                pattern_matching_result = 1
            
            if pattern_matching_result == 0:
                o : Any = obj_from_comp(ftype, each)
                (arguments[i_2].elements.append(o))
                break_0027 = True
            
            elif pattern_matching_result == 1:
                (pattern_matching_result_1, comments_1, fname_0027_4, fvalue_1) = (None, None, None, None)
                if each.tag == 8:
                    if each.fields[1].tag == 4:
                        def arrow_106(tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> bool:
                            test_expr : List[Component] = each.fields[1].fields[1]
                            def arrow_105(x: Component, y: Component) -> bool:
                                return equals(x, y)
                            
                            return len(test_expr) == 1 if (not equals_with(arrow_105, test_expr, None)) else (False)
                        
                        if arrow_106():
                            def arrow_107(tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> bool:
                                fvalue : Component = each.fields[1].fields[1][0]
                                return each.fields[1].fields[0] == fname
                            
                            if arrow_107():
                                pattern_matching_result_1 = 0
                                comments_1 = each.fields[0]
                                fname_0027_4 = each.fields[1].fields[0]
                                fvalue_1 = each.fields[1].fields[1][0]
                            
                            else: 
                                pattern_matching_result_1 = 1
                            
                        
                        else: 
                            pattern_matching_result_1 = 1
                        
                    
                    else: 
                        pattern_matching_result_1 = 1
                    
                
                else: 
                    pattern_matching_result_1 = 1
                
                if pattern_matching_result_1 == 0:
                    o_1 : Any = obj_from_comp(ftype, Component(8, comments_1, fvalue_1))
                    arguments[i_2] = o_1
                    break_0027 = True
                
                elif pattern_matching_result_1 == 1:
                    (pattern_matching_result_2, fname_0027_6, fvalue_3) = (None, None, None)
                    if each.tag == 4:
                        def arrow_103(tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> bool:
                            test_expr_1 : List[Component] = each.fields[1]
                            def arrow_102(x_1: Component, y_1: Component) -> bool:
                                return equals(x_1, y_1)
                            
                            return len(test_expr_1) == 1 if (not equals_with(arrow_102, test_expr_1, None)) else (False)
                        
                        if arrow_103():
                            def arrow_104(tname: str=tname, finfo: List[Any]=finfo, elements: List[Component]=elements) -> bool:
                                fvalue_2 : Component = each.fields[1][0]
                                return each.fields[0] == fname
                            
                            if arrow_104():
                                pattern_matching_result_2 = 0
                                fname_0027_6 = each.fields[0]
                                fvalue_3 = each.fields[1][0]
                            
                            else: 
                                pattern_matching_result_2 = 1
                            
                        
                        else: 
                            pattern_matching_result_2 = 1
                        
                    
                    else: 
                        pattern_matching_result_2 = 1
                    
                    if pattern_matching_result_2 == 0:
                        o_2 : Any = obj_from_comp(ftype, fvalue_3)
                        arguments[i_2] = o_2
                        break_0027 = True
                    
                    elif pattern_matching_result_2 == 1:
                        (pattern_matching_result_3, fvalue_5) = (None, None)
                        if each.tag == 8:
                            if each.fields[1].tag == 2:
                                if fname == AllowOmit_Name if (equals(arguments[i_2], None)) else (False):
                                    pattern_matching_result_3 = 0
                                    fvalue_5 = each
                                
                                else: 
                                    pattern_matching_result_3 = 1
                                
                            
                            else: 
                                pattern_matching_result_3 = 1
                            
                        
                        else: 
                            pattern_matching_result_3 = 1
                        
                        if pattern_matching_result_3 == 0:
                            arguments[i_2] = obj_from_comp(ftype, fvalue_5)
                            break_0027 = True
                        
                        elif pattern_matching_result_3 == 1:
                            (pattern_matching_result_4, fvalue_7) = (None, None)
                            if each.tag == 2:
                                if fname == AllowOmit_Name if (equals(arguments[i_2], None)) else (False):
                                    pattern_matching_result_4 = 0
                                    fvalue_7 = each
                                
                                else: 
                                    pattern_matching_result_4 = 1
                                
                            
                            else: 
                                pattern_matching_result_4 = 1
                            
                            if pattern_matching_result_4 == 0:
                                arguments[i_2] = obj_from_comp(ftype, fvalue_7)
                                break_0027 = True
                            
                            elif pattern_matching_result_4 == 1:
                                (pattern_matching_result_5, fvalue_10) = (None, None)
                                if each.tag == 8:
                                    if each.fields[1].tag == 7:
                                        if fname == AllowOmit_Version if (equals(arguments[i_2], None)) else (False):
                                            pattern_matching_result_5 = 0
                                            fvalue_10 = each
                                        
                                        else: 
                                            pattern_matching_result_5 = 1
                                        
                                    
                                    elif each.fields[1].tag == 6:
                                        if fname == AllowOmit_Version if (equals(arguments[i_2], None)) else (False):
                                            pattern_matching_result_5 = 0
                                            fvalue_10 = each
                                        
                                        else: 
                                            pattern_matching_result_5 = 1
                                        
                                    
                                    else: 
                                        pattern_matching_result_5 = 1
                                    
                                
                                else: 
                                    pattern_matching_result_5 = 1
                                
                                if pattern_matching_result_5 == 0:
                                    arguments[i_2] = obj_from_comp(ftype, fvalue_10)
                                    break_0027 = True
                                
                                elif pattern_matching_result_5 == 1:
                                    (pattern_matching_result_6, fvalue_13) = (None, None)
                                    if each.tag == 7:
                                        if fname == AllowOmit_Version if (equals(arguments[i_2], None)) else (False):
                                            pattern_matching_result_6 = 0
                                            fvalue_13 = each
                                        
                                        else: 
                                            pattern_matching_result_6 = 1
                                        
                                    
                                    elif each.tag == 6:
                                        if fname == AllowOmit_Version if (equals(arguments[i_2], None)) else (False):
                                            pattern_matching_result_6 = 0
                                            fvalue_13 = each
                                        
                                        else: 
                                            pattern_matching_result_6 = 1
                                        
                                    
                                    else: 
                                        pattern_matching_result_6 = 1
                                    
                                    if pattern_matching_result_6 == 0:
                                        arguments[i_2] = obj_from_comp(ftype, fvalue_13)
                                        break_0027 = True
                                    
                                
                            
                        
                    
                
            
            i_2 = (i_2 + 1) or 0
        if not break_0027:
            if unused_field is None:
                raise FromCompinentError(to_text(interpolate("%P() received invalid %P()", [tname, Component__get_kind(each)])))
            
            else: 
                unused_field_i : int = unused_field or 0
                col : List[Component] = arguments[unused_field_i]
                (col.append(each))
            
        
    for i_3 in range(0, (len(finfo_1) - 1) + 1, 1):
        pattern_input_1 : Tuple[str, Any] = finfo_1[i_3]
        ftype_1 : Any = pattern_input_1[1]
        if equals(arguments[i_3], None):
            if is_option_type(ftype_1):
                arguments[i_3] = None
            
            else: 
                raise FromCompinentError(to_text(interpolate("%P() expects a field %P(): %P()", [tname, pattern_input_1[0], name(ftype_1)])))
            
        
    return arguments


def obj_from_comp(t: Any, data: Component) -> Any:
    def arrow_108(t: Any=t, data: Component=data) -> bool:
        t_1 : Any = t
        return equals_1(get_generic_type_definition(t_1), commented_1_reflection(obj_type)) if (is_generic_type(t_1)) else (False)
    
    if arrow_108():
        eltype : Any = get_generics(t)[0]
        if data.tag == 8:
            return commented_1(0, data.fields[0], obj_from_comp(eltype, data.fields[1]))
        
        else: 
            return commented_1(0, [], obj_from_comp(eltype, data))
        
    
    elif int8_type is t:
        return (int(to_number(num_from_comp(data))) + 0x80 & 0xFF) - 0x80
    
    elif int16_type is t:
        return (int(to_number(num_from_comp(data))) + 0x8000 & 0xFFFF) - 0x8000
    
    elif int32_type is t:
        return int(to_number(num_from_comp(data)))
    
    elif class_type("System.Int64") is t:
        return num_from_comp(data)
    
    elif float64_type is t:
        return to_number_1(num_from_comp(data))
    
    elif float64_type is t:
        return num_from_comp(data)
    
    elif class_type("System.Decimal") is t:
        return num_from_comp(data)
    
    elif bool_type is t:
        return bool_from_comp(data)
    
    elif char_type is t:
        return char_from_comp(data)
    
    elif unit_type is t:
        raise FromCompinentError("component does not support unit type.")
    
    elif string_type is t:
        return string_from_comp(data)
    
    elif is_array(t):
        eltype_1 : Any = get_generics(t)[0]
        (pattern_matching_result, spec_1) = (None, None)
        if data.tag == 7:
            if equals_1(eltype_1, specifier_reflection()):
                pattern_matching_result = 0
                spec_1 = data.fields[0]
            
            else: 
                pattern_matching_result = 1
            
        
        else: 
            pattern_matching_result = 1
        
        if pattern_matching_result == 0:
            return spec_1
        
        elif pattern_matching_result == 1:
            active_pattern_result1058 : Any = _007CNotCList_007CIsCList_007C(data)
            if active_pattern_result1058.tag == 1:
                if eltype_1 is int32_type:
                    def arrow_109(i: int, t: Any=t, data: Component=data) -> int:
                        return int(to_number(num_from_comp(active_pattern_result1058.fields[0][i])))
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_109, Int32Array)
                
                elif eltype_1 == class_type("System.Int64"):
                    def arrow_110(i_1: int, t: Any=t, data: Component=data) -> Any:
                        return from_number(to_number_1(num_from_comp(active_pattern_result1058.fields[0][i_1])), False)
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_110, None)
                
                elif eltype_1 is int16_type:
                    def arrow_111(i_2: int, t: Any=t, data: Component=data) -> int:
                        return (int(to_number(num_from_comp(active_pattern_result1058.fields[0][i_2]))) + 0x8000 & 0xFFFF) - 0x8000
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_111, Int16Array)
                
                elif eltype_1 is int8_type:
                    def arrow_112(i_3: int, t: Any=t, data: Component=data) -> int:
                        return (int(to_number(num_from_comp(active_pattern_result1058.fields[0][i_3]))) + 0x80 & 0xFF) - 0x80
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_112, Int8Array)
                
                elif eltype_1 is uint32_type:
                    def arrow_113(i_4: int, t: Any=t, data: Component=data) -> int:
                        return int(to_number(num_from_comp(active_pattern_result1058.fields[0][i_4]))+0x100000000 if to_number(num_from_comp(active_pattern_result1058.fields[0][i_4])) < 0 else to_number(num_from_comp(active_pattern_result1058.fields[0][i_4])))
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_113, Uint32Array)
                
                elif eltype_1 == class_type("System.UInt64"):
                    def arrow_114(i_5: int, t: Any=t, data: Component=data) -> Any:
                        return from_number(to_number_1(num_from_comp(active_pattern_result1058.fields[0][i_5])), True)
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_114, None)
                
                elif eltype_1 is uint8_type:
                    def arrow_115(i_6: int, t: Any=t, data: Component=data) -> int:
                        return int(to_number(num_from_comp(active_pattern_result1058.fields[0][i_6]))+0x100 if to_number(num_from_comp(active_pattern_result1058.fields[0][i_6])) < 0 else to_number(num_from_comp(active_pattern_result1058.fields[0][i_6]))) & 0xFF
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_115, Uint8Array)
                
                elif eltype_1 is uint16_type:
                    def arrow_116(i_7: int, t: Any=t, data: Component=data) -> int:
                        return int(to_number(num_from_comp(active_pattern_result1058.fields[0][i_7]))+0x10000 if to_number(num_from_comp(active_pattern_result1058.fields[0][i_7])) < 0 else to_number(num_from_comp(active_pattern_result1058.fields[0][i_7]))) & 0xFFFF
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_116, Uint16Array)
                
                elif eltype_1 is float64_type:
                    def arrow_117(i_8: int, t: Any=t, data: Component=data) -> float:
                        return to_number_1(num_from_comp(active_pattern_result1058.fields[0][i_8]))
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_117, Float64Array)
                
                elif eltype_1 is float64_type:
                    def arrow_118(i_9: int, t: Any=t, data: Component=data) -> float:
                        return to_number_1(num_from_comp(active_pattern_result1058.fields[0][i_9]))
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_118, Float64Array)
                
                elif eltype_1 == class_type("System.Decimal"):
                    def arrow_119(i_10: int, t: Any=t, data: Component=data) -> Any:
                        return num_from_comp(active_pattern_result1058.fields[0][i_10])
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_119, None)
                
                elif eltype_1 is string_type:
                    def arrow_120(i_11: int, t: Any=t, data: Component=data) -> str:
                        return string_from_comp(active_pattern_result1058.fields[0][i_11])
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_120, None)
                
                elif eltype_1 is bool_type:
                    def arrow_121(i_12: int, t: Any=t, data: Component=data) -> bool:
                        return bool_from_comp(active_pattern_result1058.fields[0][i_12])
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_121, None)
                
                elif eltype_1 is unit_type:
                    raise FromCompinentError("component does not support unit type.")
                
                elif eltype_1 is char_type:
                    def arrow_122(i_13: int, t: Any=t, data: Component=data) -> str:
                        return char_from_comp(active_pattern_result1058.fields[0][i_13])
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_122, None)
                
                else: 
                    def arrow_123(i_14: int, t: Any=t, data: Component=data) -> Any:
                        return obj_from_comp(eltype_1, active_pattern_result1058.fields[0][i_14])
                    
                    return initialize(len(active_pattern_result1058.fields[0]), arrow_123, None)
                
            
            else: 
                raise FromCompinentError(to_text(interpolate("convert %P() to %P()", [Component__get_kind(data), t])))
            
        
    
    elif is_option_type(t):
        if data.tag == 0:
            return None
        
        else: 
            return some(obj_from_comp(get_generics(t)[0], data))
        
    
    elif equals_1(t, class_type("FablePykg.Comp.version")):
        if data.tag == 6:
            return data.fields[0]
        
        else: 
            raise FromCompinentError(to_text(interpolate("convert %P() to %P()", [Component__get_kind(data), t])))
        
    
    else: 
        def arrow_124(t: Any=t, data: Component=data) -> bool:
            t_2 : Any = t
            return equals_1(get_generic_type_definition(t_2), list_type(obj_type)) if (is_generic_type(t_2)) else (False)
        
        if arrow_124():
            eltype_3 : Any = get_generics(t)[0]
            (pattern_matching_result_1, spec_3) = (None, None)
            if data.tag == 7:
                if equals_1(eltype_3, specifier_reflection()):
                    pattern_matching_result_1 = 0
                    spec_3 = data.fields[0]
                
                else: 
                    pattern_matching_result_1 = 1
                
            
            else: 
                pattern_matching_result_1 = 1
            
            if pattern_matching_result_1 == 0:
                return of_array(spec_3)
            
            elif pattern_matching_result_1 == 1:
                active_pattern_result1064 : Any = _007CNotCList_007CIsCList_007C(data)
                if active_pattern_result1064.tag == 1:
                    o : FSharpList[Any] = empty()
                    for i_15 in range(len(active_pattern_result1064.fields[0]) - 1, 0 - 1, -1):
                        o = cons(obj_from_comp(eltype_3, active_pattern_result1064.fields[0][i_15]), o)
                    return o
                
                else: 
                    raise FromCompinentError(to_text(interpolate("convert %P() to %P()", [Component__get_kind(data), t])))
                
            
        
        else: 
            def arrow_125(t: Any=t, data: Component=data) -> bool:
                t_3 : Any = t
                return equals_1(get_generic_type_definition(t_3), lift_array_1_reflection(obj_type)) if (is_generic_type(t_3)) else (False)
            
            if arrow_125():
                raise FromCompinentError("lift_array is not allowed outside fields")
            
            elif is_record(t):
                tname : str = name(t)
                elements_2 : List[Component]
                (pattern_matching_result_2, elements_1, tname_0027_1) = (None, None, None)
                if data.tag == 4:
                    if data.fields[0] == tname:
                        pattern_matching_result_2 = 0
                        elements_1 = data.fields[1]
                        tname_0027_1 = data.fields[0]
                    
                    else: 
                        pattern_matching_result_2 = 1
                    
                
                else: 
                    pattern_matching_result_2 = 1
                
                if pattern_matching_result_2 == 0:
                    elements_2 = elements_1
                
                elif pattern_matching_result_2 == 1:
                    raise FromCompinentError(to_text(interpolate("convert %P() to %P()", [Component__get_kind(data), t])))
                
                arguments : List[Any] = extract_field_arguments(tname, get_record_elements(t), elements_2)
                ignore()
                return make_record(t, arguments)
            
            elif is_tuple(t):
                eltypes : List[Any] = get_tuple_elements(t)
                seq_3 : List[Component]
                if data.tag == 5:
                    seq_3 = data.fields[0]
                
                else: 
                    raise FromCompinentError(to_text(interpolate("convert %P() to %P()", [Component__get_kind(data), t])))
                
                def arrow_126(i_16: int, t: Any=t, data: Component=data) -> Any:
                    return obj_from_comp(eltypes[i_16], seq_3[i_16])
                
                return make_tuple(initialize(len(seq_3), arrow_126, None), t)
            
            elif is_union(t):
                pattern_input : Tuple[str, List[Component]]
                if data.tag == 4:
                    pattern_input = (data.fields[0], data.fields[1])
                
                else: 
                    raise FromCompinentError(to_text(interpolate("convert %P() to %P()", [Component__get_kind(data), t])))
                
                cname_0027_2 : str = pattern_input[0].lower()
                def predicate(case: Any, t: Any=t, data: Component=data) -> bool:
                    return name(case).lower() == cname_0027_2
                
                match_value : Optional[Any] = try_find(predicate, get_union_cases(t))
                if match_value is not None:
                    case_1 : Any = match_value
                    finfo_1 : List[Any] = get_union_case_fields(case_1)
                    return make_union(case_1, extract_field_arguments((name(t) + ".") + cname_0027_2, finfo_1, pattern_input[1]))
                
                else: 
                    raise FromCompinentError(to_text(interpolate("unknown constructor %P()", [cname_0027_2])))
                
            
            else: 
                raise FromCompinentError(to_text(interpolate("unsupported data type fromJson: %P()", [t])))
            
        
    


def obj_to_comp(t_mut: Any, o_mut: Any) -> Component:
    while True:
        (t, o) = (t_mut, o_mut)
        if int8_type is t:
            return Component(1, Decimal(o))
        
        elif int16_type is t:
            return Component(1, Decimal(o))
        
        elif int32_type is t:
            return Component(1, Decimal(o))
        
        elif class_type("System.Int64") is t:
            return Component(1, Decimal(to_number_2(o)))
        
        elif float64_type is t:
            return Component(1, Decimal(o))
        
        elif float64_type is t:
            return Component(1, Decimal(o))
        
        elif class_type("System.Decimal") is t:
            return Component(1, o)
        
        elif bool_type is t:
            return Component(3, o)
        
        elif char_type is t:
            return Component(2, o)
        
        elif unit_type is t:
            raise ToComponentError("component does not support unit type.")
        
        elif string_type is t:
            return Component(2, o)
        
        elif equals_1(class_type("FablePykg.Comp.version"), t):
            return Component(6, o)
        
        elif equals_1(Component_reflection(), t):
            return o
        
        elif is_array(t):
            eltype : Any = get_element_type(t)
            if equals_1(eltype, specifier_reflection()):
                return Component(7, o)
            
            elif eltype is int32_type:
                def mapping(it: int, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it)
                
                return Component(5, map(mapping, o, None))
            
            elif eltype == class_type("System.Int64"):
                def mapping_1(it_1: Any, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_1)
                
                return Component(5, map(mapping_1, o, None))
            
            elif eltype is int16_type:
                def mapping_2(it_2: int, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_2)
                
                return Component(5, map(mapping_2, o, None))
            
            elif eltype is int8_type:
                def mapping_3(it_3: int, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_3)
                
                return Component(5, map(mapping_3, o, None))
            
            elif eltype is uint32_type:
                def mapping_4(it_4: int, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_4)
                
                return Component(5, map(mapping_4, o, None))
            
            elif eltype == class_type("System.UInt64"):
                def mapping_5(it_5: Any, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_5)
                
                return Component(5, map(mapping_5, o, None))
            
            elif eltype is uint8_type:
                def mapping_6(it_6: int, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_6)
                
                return Component(5, map(mapping_6, o, None))
            
            elif eltype is uint16_type:
                def mapping_7(it_7: int, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_7)
                
                return Component(5, map(mapping_7, o, None))
            
            elif eltype is float64_type:
                def mapping_8(it_8: float, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_8)
                
                return Component(5, map(mapping_8, o, None))
            
            elif eltype is float64_type:
                def mapping_9(it_9: float, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_9)
                
                return Component(5, map(mapping_9, o, None))
            
            elif eltype == class_type("System.Decimal"):
                def mapping_10(it_10: Any, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_10)
                
                return Component(5, map(mapping_10, o, None))
            
            elif eltype is string_type:
                def mapping_11(it_11: str, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_11)
                
                return Component(5, map(mapping_11, o, None))
            
            elif eltype is bool_type:
                def mapping_12(it_12: bool, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_12)
                
                return Component(5, map(mapping_12, o, None))
            
            elif eltype is unit_type:
                raise ToComponentError("component does not support unit type.")
            
            elif eltype is char_type:
                def mapping_13(it_13: str, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_13)
                
                return Component(5, map(mapping_13, o, None))
            
            else: 
                def mapping_14(it_14: Any, t: Any=t, o: Any=o) -> Component:
                    return obj_to_comp(eltype, it_14)
                
                return Component(5, map(mapping_14, o, None))
            
        
        elif is_option_type(t):
            eltype_1 : Any = get_generics(t)[0]
            match_value : Optional[Any] = o
            if match_value is not None:
                t_mut = eltype_1
                o_mut = value_31(match_value)
                continue
            
            else: 
                return Component(0)
            
        
        else: 
            def arrow_127(t: Any=t, o: Any=o) -> bool:
                t_1 : Any = t
                return equals_1(get_generic_type_definition(t_1), commented_1_reflection(obj_type)) if (is_generic_type(t_1)) else (False)
            
            if arrow_127():
                match_value_1 : commented_1[Any] = o
                return Component(8, match_value_1.fields[0], obj_to_comp(get_generics(t)[0], match_value_1.fields[1]))
            
            elif equals_1(get_generic_type_definition(t), list_type(obj_type)) if (is_generic_type(t)) else (False):
                eltype_3 : Any = get_generics(t)[0]
                if equals_1(eltype_3, specifier_reflection()):
                    return Component(7, to_array(o))
                
                else: 
                    def mapping_15(it_15: Any, t: Any=t, o: Any=o) -> Component:
                        return obj_to_comp(eltype_3, it_15)
                    
                    return Component(5, to_array(map_1(mapping_15, o)))
                
            
            else: 
                def arrow_128(t: Any=t, o: Any=o) -> bool:
                    t_2 : Any = t
                    return equals_1(get_generic_type_definition(t_2), lift_array_1_reflection(obj_type)) if (is_generic_type(t_2)) else (False)
                
                if arrow_128():
                    raise ToComponentError("lift_array is not allowed outside fields")
                
                elif is_record(t):
                    def arrow_132(t: Any=t, o: Any=o) -> IEnumerable[Component]:
                        def arrow_131(fi: Any) -> IEnumerable[Component]:
                            def arrow_129(__unit: Any=None) -> bool:
                                t_3 : Any = fi[1]
                                return equals_1(get_generic_type_definition(t_3), lift_array_1_reflection(obj_type)) if (is_generic_type(t_3)) else (False)
                            
                            if arrow_129():
                                eltype_4 : Any = get_generics(fi[1])[0]
                                def arrow_130(elt: Any) -> Component:
                                    return obj_to_comp(eltype_4, elt)
                                
                                return map_2(arrow_130, get_record_field(o, fi).elements)
                            
                            else: 
                                f_1 : Component = obj_to_comp(fi[1], get_record_field(o, fi))
                                return singleton(Component(4, name(fi), [f_1]))
                            
                        
                        return collect(arrow_131, get_record_elements(t))
                    
                    fields : List[Component] = to_array_1(delay(arrow_132))
                    return Component(4, name(t), fields)
                
                elif is_tuple(t):
                    eltypes : List[Any] = get_tuple_elements(t)
                    def mapping_16(i_1: int, e: Any, t: Any=t, o: Any=o) -> Component:
                        return obj_to_comp(eltypes[i_1], e)
                    
                    return Component(5, map_indexed(mapping_16, get_tuple_fields(o), None))
                
                elif is_union(t):
                    pattern_input : Tuple[Any, List[Any]] = get_union_fields(o, t)
                    case : Any = pattern_input[0]
                    def arrow_139(t: Any=t, o: Any=o) -> IEnumerable[Component]:
                        i_2 : int = 0
                        def arrow_138(fi_1: Any) -> IEnumerable[Component]:
                            f_2 : Any = pattern_input[1][i_2]
                            def arrow_133(__unit: Any=None) -> bool:
                                t_4 : Any = fi_1[1]
                                return equals_1(get_generic_type_definition(t_4), lift_array_1_reflection(obj_type)) if (is_generic_type(t_4)) else (False)
                            
                            def arrow_135(__unit: Any=None) -> IEnumerable[Component]:
                                eltype_5 : Any = get_generics(fi_1[1])[0]
                                def arrow_134(elt_1: Any) -> Component:
                                    return obj_to_comp(eltype_5, elt_1)
                                
                                return map_2(arrow_134, f_2.elements)
                            
                            def arrow_136(__unit: Any=None) -> IEnumerable[Component]:
                                f_0027_1 : Component = obj_to_comp(fi_1[1], f_2)
                                return singleton(Component(4, name(fi_1), [f_0027_1]))
                            
                            def arrow_137(__unit: Any=None) -> IEnumerable[Component]:
                                nonlocal i_2
                                i_2 = (i_2 + 1) or 0
                                return empty_1()
                            
                            return append(arrow_135() if (arrow_133()) else (arrow_136()), delay(arrow_137))
                        
                        return collect(arrow_138, get_union_case_fields(case))
                    
                    fields_1 : List[Component] = to_array_1(delay(arrow_139))
                    return Component(4, name(case).lower(), fields_1)
                
                else: 
                    raise ToComponentError(to_text(interpolate("unsupported data type fromJson: %P()", [t])))
                
            
        
        break


space2 : Doc = Doc(5, seg("  "))

def serialize_comp(x: Component) -> Doc:
    if x.tag == 7:
        def arrow_140(s_1: str, x: Component=x) -> Doc:
            return seg(s_1)
        
        def mapping(x_3: specifier, x: Component=x) -> str:
            return specifier__get_Show(x_3)
        
        arr : List[Doc] = map(arrow_140, map(mapping, x.fields[0], None), None)
        return separray(seg(" \u0026\u0026 "), arr)
    
    elif x.tag == 8:
        def arrow_142(s_2: str, x: Component=x) -> Doc:
            return seg(s_2)
        
        return vsep(of_array([vsep(of_array(map(arrow_142, x.fields[0], None))), serialize_comp(x.fields[1])]))
    
    elif x.tag == 1:
        return seg(to_string_1(x.fields[0]))
    
    elif x.tag == 3:
        if x.fields[0]:
            return seg("true")
        
        else: 
            return seg("false")
        
    
    elif x.tag == 2:
        return seg(("\"" + escape_string(x.fields[0])) + "\"")
    
    elif x.tag == 0:
        return seg("null")
    
    elif x.tag == 5:
        def arrow_144(x: Component=x) -> bool:
            test_expr : List[Component] = x.fields[0]
            def arrow_143(x_1: Component, y: Component) -> bool:
                return equals(x_1, y)
            
            return len(test_expr) == 1 if (not equals_with(arrow_143, test_expr, None)) else (False)
        
        if arrow_144():
            elt : Component = x.fields[0][0]
            return Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(seg("["), align(serialize_comp(elt))), seg("]"))
        
        else: 
            def arrow_145(x_5: Component, x: Component=x) -> Doc:
                return serialize_comp(x_5)
            
            it : Doc = indent(2, vsep(of_array(map(arrow_145, x.fields[0], None))))
            return vsep(of_array([seg("["), it, seg("]")]))
        
    
    elif x.tag == 4:
        def arrow_147(x: Component=x) -> bool:
            test_expr_1 : List[Component] = x.fields[1]
            def arrow_146(x_2: Component, y_1: Component) -> bool:
                return equals(x_2, y_1)
            
            return len(test_expr_1) == 1 if (not equals_with(arrow_146, test_expr_1, None)) else (False)
        
        if arrow_147():
            elt_1 : Component = x.fields[1][0]
            return Doc_op_Addition_Z32C4A9C0(seg(x.fields[0]), align(serialize_comp(elt_1)))
        
        else: 
            def arrow_148(x_7: Component, x: Component=x) -> Doc:
                return serialize_comp(x_7)
            
            it_1 : Doc = indent(2, vsep(of_array(map(arrow_148, x.fields[1], None))))
            return vsep(of_array([Doc_op_Addition_Z32C4A9C0(seg(x.fields[0]), seg("{")), it_1, seg("}")]))
        
    
    else: 
        return seg(to_string(x.fields[0]))
    


