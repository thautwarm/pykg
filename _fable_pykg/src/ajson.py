from __future__ import annotations
from typing import (Any, List, Tuple, Callable, TypeVar, Generic, Optional)
from ..fable_modules.fable_library.array import (contains, initialize, map, fill, find_index, find as find_1, map_indexed)
from ..fable_modules.fable_library.decimal import (Decimal, to_number)
from ..fable_modules.fable_library.double import parse as parse_1
from ..fable_modules.fable_library.list import (FSharpList, is_empty, head, tail, empty, cons, map as map_1)
from ..fable_modules.fable_library.long import (parse, equals, from_bits, to_int, from_value, from_integer)
from ..fable_modules.fable_library.option import (some, value as value_29)
from ..fable_modules.fable_library.reflection import (TypeInfo, class_type, float64_type, bool_type, string_type, array_type, tuple_type, union_type, int8_type, int16_type, int32_type, char_type, unit_type, is_array, get_element_type, uint32_type, uint8_type, uint16_type, is_generic_type, equals as equals_1, get_generic_type_definition, obj_type, option_type, get_generics, list_type, is_record, name, get_record_elements, make_record, is_tuple, get_tuple_elements, make_tuple, is_union, get_union_cases, get_union_case_fields, make_union, get_record_field, get_tuple_fields, get_union_fields)
from ..fable_modules.fable_library.seq import (find, map as map_2)
from ..fable_modules.fable_library.string import (to_text, interpolate, join)
from ..fable_modules.fable_library.system_text import (StringBuilder__ctor, StringBuilder__Append_244C7CD6, StringBuilder__ctor_Z524259A4, StringBuilder__Append_Z721C83C5)
from ..fable_modules.fable_library.types import (Union, to_string, FSharpRef, Int32Array, Int16Array, Int8Array, Uint32Array, Uint8Array, Uint16Array, Float64Array)
from ..fable_modules.fable_library.util import (string_hash, ignore, uncurry, get_enumerator, dispose, int64_to_string)

_A = TypeVar("_A")

__A = TypeVar("__A")

_B = TypeVar("_B")

def expr_23() -> TypeInfo:
    return union_type("AJson.Json", [], Json, lambda: [[["Item", class_type("System.Int64")]], [["Item", float64_type]], [["Item", bool_type]], [["Item", string_type]], [], [["Item", array_type(Json_reflection())]], [["Item", array_type(tuple_type(string_type, Json_reflection()))]]])


class Json(Union):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["JInt", "JFloat", "JBool", "JStr", "JNull", "JList", "JDict"]
    

Json_reflection = expr_23

def Json__get_kind(this: Json) -> str:
    if this.tag == 1:
        return "float"
    
    elif this.tag == 2:
        return "bool"
    
    elif this.tag == 3:
        return "string"
    
    elif this.tag == 4:
        return "null"
    
    elif this.tag == 5:
        return "list"
    
    elif this.tag == 6:
        return "dict"
    
    else: 
        return "int"
    


def Parsec_pChar_(c: str) -> Callable[[int, str], Tuple[int, None]]:
    def apply(i: int, c: str=c) -> Callable[[str], Tuple[int, None]]:
        def arrow_24(s: str, i: int=i) -> Tuple[int, None]:
            if True if (i >= len(s)) else (s[i] != c):
                raise Exception("unexpected match")
            
            else: 
                return (i + 1, None)
            
        
        return arrow_24
    
    return apply


def Parsec_pStr_(pat: str) -> Callable[[int, str], Tuple[int, None]]:
    def apply(i: int, pat: str=pat) -> Callable[[str], Tuple[int, None]]:
        def arrow_25(s: str, i: int=i) -> Tuple[int, None]:
            if True if ((i + len(pat)) > len(s)) else (s[i:((i + len(pat)) - 1) + 1] != pat):
                raise Exception("unexpected match")
            
            else: 
                return (i + len(pat), None)
            
        
        return arrow_25
    
    return apply


def Parsec_pChar(c: str) -> Callable[[int, str], Tuple[int, str]]:
    def apply(i: int, c: str=c) -> Callable[[str], Tuple[int, str]]:
        def arrow_26(s: str, i: int=i) -> Tuple[int, str]:
            if True if (i >= len(s)) else (s[i] != c):
                raise Exception("unexpected match")
            
            else: 
                return (i + 1, c)
            
        
        return arrow_26
    
    return apply


def Parsec_pCharset_(cs: List[str]) -> Callable[[int, str], Tuple[int, None]]:
    def apply(i: int, cs: List[str]=cs) -> Callable[[str], Tuple[int, None]]:
        def arrow_30(s: str, i: int=i) -> Tuple[int, None]:
            if i >= len(s):
                raise Exception("unexpected match")
            
            else: 
                class ObjectExpr29:
                    @property
                    def Equals(self) -> Any:
                        def arrow_27(x: str, y: str) -> bool:
                            return x == y
                        
                        return arrow_27
                    
                    @property
                    def GetHashCode(self) -> Any:
                        def arrow_28(x: str) -> int:
                            return string_hash(x)
                        
                        return arrow_28
                    
                if contains(s[i], cs, ObjectExpr29()):
                    return (i + 1, None)
                
                else: 
                    raise Exception("unexpected match")
                
            
        
        return arrow_30
    
    return apply


def Parsec_pCharset(cs: List[str]) -> Callable[[int, str], Tuple[int, str]]:
    def apply(i: int, cs: List[str]=cs) -> Callable[[str], Tuple[int, str]]:
        def arrow_34(s: str, i: int=i) -> Tuple[int, str]:
            if i >= len(s):
                raise Exception("unexpected match")
            
            else: 
                class ObjectExpr33:
                    @property
                    def Equals(self) -> Any:
                        def arrow_31(x: str, y: str) -> bool:
                            return x == y
                        
                        return arrow_31
                    
                    @property
                    def GetHashCode(self) -> Any:
                        def arrow_32(x: str) -> int:
                            return string_hash(x)
                        
                        return arrow_32
                    
                if contains(s[i], cs, ObjectExpr33()):
                    return (i + 1, s[i])
                
                else: 
                    raise Exception(to_text(interpolate("unexpected match %P()", [s[i]])))
                
            
        
        return arrow_34
    
    return apply


def Parsec_pIgnore(p: Callable[[int, str], Tuple[int, _A]]) -> Callable[[int, str], Tuple[int, None]]:
    def apply(i: int, p: Callable[[int, str], Tuple[int, _A]]=p) -> Callable[[str], Tuple[int, None]]:
        def arrow_35(s: str, i: int=i) -> Tuple[int, None]:
            return (p(i, s)[0], None)
        
        return arrow_35
    
    return apply


def Parsec_pSeq_(ps: FSharpList[Callable[[int, str], Tuple[int, None]]]) -> Callable[[int, str], Tuple[int, None]]:
    def apply(i: int, ps: FSharpList[Callable[[int, str], Tuple[int, None]]]=ps) -> Callable[[str], Tuple[int, None]]:
        def arrow_36(s: str, i: int=i) -> Tuple[int, None]:
            def loop(i_1_mut: int, ps_1_mut: FSharpList[Callable[[int, str], Tuple[int, __A]]]) -> Tuple[int, None]:
                while True:
                    (i_1, ps_1) = (i_1_mut, ps_1_mut)
                    if i_1 >= len(s):
                        raise Exception("unexpected match")
                    
                    elif is_empty(ps_1):
                        return (i_1, None)
                    
                    else: 
                        i_1_mut = head(ps_1)(i_1)(s)[0]
                        ps_1_mut = tail(ps_1)
                        continue
                    
                    break
            
            return loop(i, ps)
        
        return arrow_36
    
    return apply


def Parsec_pSepRep(sep: Callable[[int, str], Tuple[int, bool]], p: Callable[[int, str], Tuple[int, _A]]) -> Callable[[int, str], Tuple[int, List[_A]]]:
    def apply(i: int, sep: Callable[[int, str], Tuple[int, bool]]=sep, p: Callable[[int, str], Tuple[int, _A]]=p) -> Callable[[str], Tuple[int, List[_A]]]:
        def arrow_37(s: str, i: int=i) -> Tuple[int, List[_A]]:
            res : List[_A] = []
            def loop(i_1_mut: int) -> Tuple[int, List[_A]]:
                while True:
                    (i_1,) = (i_1_mut,)
                    if i_1 >= len(s):
                        raise Exception("unexpected match")
                    
                    else: 
                        pattern_input : Tuple[int, _A] = p(i_1, s)
                        (res.append(pattern_input[1]))
                        pattern_input_1 : Tuple[int, bool] = sep(pattern_input[0], s)
                        i_3 : int = pattern_input_1[0] or 0
                        if pattern_input_1[1]:
                            i_1_mut = i_3
                            continue
                        
                        else: 
                            return (i_3, res)
                        
                    
                    break
            
            return loop(i)
        
        return arrow_37
    
    return apply


def apply(i: int) -> Callable[[str], Tuple[int, None]]:
    def arrow_38(s: str, i: int=i) -> Tuple[int, None]:
        def loop(i_1_mut: int) -> Tuple[int, None]:
            while True:
                (i_1,) = (i_1_mut,)
                if i_1 >= len(s):
                    return (i_1, None)
                
                else: 
                    match_value : str = s[i_1]
                    (pattern_matching_result,) = (None,)
                    if match_value == "\t":
                        pattern_matching_result = 0
                    
                    elif match_value == "\n":
                        pattern_matching_result = 0
                    
                    elif match_value == "\r":
                        pattern_matching_result = 0
                    
                    elif match_value == " ":
                        pattern_matching_result = 0
                    
                    else: 
                        pattern_matching_result = 1
                    
                    if pattern_matching_result == 0:
                        i_1_mut = i_1 + 1
                        continue
                    
                    elif pattern_matching_result == 1:
                        return (i_1, None)
                    
                
                break
        
        return loop(i)
    
    return arrow_38


Parsec_pSpc : Callable[[int, str], Tuple[int, None]] = apply

def Parsec_allowSPC(p: Callable[[int, str], Tuple[int, _A]]) -> Callable[[int, str], Tuple[int, _A]]:
    def apply(i: int, p: Callable[[int, str], Tuple[int, _A]]=p) -> Callable[[str], Tuple[int, _A]]:
        def arrow_39(s: str, i: int=i) -> Tuple[int, _A]:
            pattern_input_1 : Tuple[int, _A] = p(Parsec_pSpc(i)(s)[0], s)
            return (Parsec_pSpc(pattern_input_1[0])(s)[0], pattern_input_1[1])
        
        return arrow_39
    
    return apply


def Parsec_la1(dispatch: Callable[[str, int, str], Tuple[int, _A]]) -> Callable[[int, str], Tuple[int, _A]]:
    def apply(i: int, dispatch: Callable[[str, int, str], Tuple[int, _A]]=dispatch) -> Callable[[str], Tuple[int, _A]]:
        def arrow_40(s: str, i: int=i) -> Tuple[int, _A]:
            if i >= len(s):
                raise Exception("unexpected match")
            
            return dispatch(s[i], i, s)
        
        return arrow_40
    
    return apply


def apply(i: int) -> Callable[[str], Tuple[int, str]]:
    def arrow_42(s: str, i: int=i) -> Tuple[int, str]:
        if i >= len(s):
            raise Exception("unexpected match")
        
        def loop(j_mut: int) -> int:
            while True:
                (j,) = (j_mut,)
                if j >= len(s):
                    return j
                
                else: 
                    match_value : str = s[j]
                    (pattern_matching_result,) = (None,)
                    if match_value == "-":
                        pattern_matching_result = 0
                    
                    elif match_value == ".":
                        pattern_matching_result = 0
                    
                    elif match_value == "E":
                        pattern_matching_result = 0
                    
                    elif match_value == "e":
                        pattern_matching_result = 0
                    
                    else: 
                        def arrow_41(j: int=j) -> bool:
                            c : str = match_value
                            return c >= "0" if (c <= "9") else (False)
                        
                        if arrow_41():
                            pattern_matching_result = 1
                        
                        else: 
                            pattern_matching_result = 2
                        
                    
                    if pattern_matching_result == 0:
                        j_mut = j + 1
                        continue
                    
                    elif pattern_matching_result == 1:
                        j_mut = j + 1
                        continue
                    
                    elif pattern_matching_result == 2:
                        return j
                    
                
                break
        
        i_1 : int = loop(i) or 0
        return (i_1, s[i:(i_1 - 1) + 1])
    
    return arrow_42


Parsec_pNumber : Callable[[int, str], Tuple[int, str]] = apply

def apply(i: int) -> Callable[[str], Tuple[int, str]]:
    def arrow_43(s: str, i: int=i) -> Tuple[int, str]:
        if True if (i >= len(s)) else (s[i] != "\""):
            raise Exception("incomplete parsing for string")
        
        buf : Any = StringBuilder__ctor()
        find_end : bool = False
        i_1 : int = (i + 1) or 0
        while not find_end if (i_1 < len(s)) else (False):
            match_value : str = s[i_1]
            if match_value == "\"":
                find_end = True
                i_1 = (i_1 + 1) or 0
            
            elif match_value == "\\":
                if (i_1 + 1) >= len(s):
                    raise Exception("incomplete escape for string")
                
                else: 
                    match_value_1 : str = s[i_1 + 1]
                    if match_value_1 == "\"":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\""))
                    
                    elif match_value_1 == "\\":
                        ignore(StringBuilder__Append_244C7CD6(buf, "\\"))
                    
                    elif match_value_1 == "b":
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
                    
                    i_1 = (i_1 + 2) or 0
                
            
            else: 
                ignore(StringBuilder__Append_244C7CD6(buf, match_value))
                i_1 = (i_1 + 1) or 0
            
        if find_end:
            return (i_1, to_string(buf))
        
        else: 
            raise Exception("incomplete string")
        
    
    return arrow_43


Parsec_pStr : Callable[[int, str], Tuple[int, str]] = apply

def Parsec_pMap(f: Callable[[_A], _B], p: Callable[[int, str], Tuple[int, _A]]) -> Callable[[int, str], Tuple[int, _B]]:
    def apply(i: int, f: Callable[[_A], _B]=f, p: Callable[[int, str], Tuple[int, _A]]=p) -> Callable[[str], Tuple[int, _B]]:
        def arrow_44(s: str, i: int=i) -> Tuple[int, _B]:
            pattern_input : Tuple[int, _A] = p(i, s)
            return (pattern_input[0], f(pattern_input[1]))
        
        return arrow_44
    
    return apply


def Parsec_pRef(p: FSharpRef[Callable[[int, str], Tuple[int, _A]]]) -> Callable[[int, str], Tuple[int, _A]]:
    def apply(i: int, p: FSharpRef[Callable[[int, str], Tuple[int, _A]]]=p) -> Callable[[str], Tuple[int, _A]]:
        def arrow_45(s: str, i: int=i) -> Tuple[int, _A]:
            return p.contents(i)(s)
        
        return arrow_45
    
    return apply


def f(_arg1: str) -> bool:
    if _arg1 == ",":
        return True
    
    elif _arg1 == "]":
        return False
    
    else: 
        raise Exception("impossible")
    


Parsec_Json_pListSep : Callable[[int, str], Tuple[int, _B]] = Parsec_pMap(f, uncurry(2, Parsec_pCharset([",", "]"])))

def f(_arg1: str) -> bool:
    if _arg1 == ",":
        return True
    
    elif _arg1 == "}":
        return False
    
    else: 
        raise Exception("impossible")
    


Parsec_Json_pDictSep : Callable[[int, str], Tuple[int, _B]] = Parsec_pMap(f, uncurry(2, Parsec_pCharset([",", "}"])))

def f(s: str) -> Any:
    return parse(s, 511, False, 64)


Parsec_Json_jInt : Callable[[int, str], Tuple[int, _B]] = Parsec_pMap(f, uncurry(2, Parsec_pNumber))

def f(s: str) -> float:
    return parse_1(s)


Parsec_Json_jFloat : Callable[[int, str], Tuple[int, _B]] = Parsec_pMap(f, uncurry(2, Parsec_pNumber))

def apply(i: int) -> Callable[[str], Tuple[int, Json]]:
    def arrow_47(s: str, i: int=i) -> Tuple[int, Json]:
        if i >= len(s):
            raise Exception("unexpected match")
        
        start : int = i or 0
        def loop(isfloat_mut: bool, j_mut: int) -> Tuple[bool, int]:
            while True:
                (isfloat, j) = (isfloat_mut, j_mut)
                if j >= len(s):
                    return (isfloat, j)
                
                else: 
                    match_value : str = s[j]
                    (pattern_matching_result,) = (None,)
                    if match_value == "-":
                        pattern_matching_result = 1
                    
                    elif match_value == ".":
                        pattern_matching_result = 0
                    
                    elif match_value == "E":
                        pattern_matching_result = 1
                    
                    elif match_value == "e":
                        pattern_matching_result = 1
                    
                    else: 
                        def arrow_46(isfloat: bool=isfloat, j: int=j) -> bool:
                            c : str = match_value
                            return c >= "0" if (c <= "9") else (False)
                        
                        if arrow_46():
                            pattern_matching_result = 2
                        
                        else: 
                            pattern_matching_result = 3
                        
                    
                    if pattern_matching_result == 0:
                        isfloat_mut = True
                        j_mut = j + 1
                        continue
                    
                    elif pattern_matching_result == 1:
                        isfloat_mut = isfloat
                        j_mut = j + 1
                        continue
                    
                    elif pattern_matching_result == 2:
                        isfloat_mut = isfloat
                        j_mut = j + 1
                        continue
                    
                    elif pattern_matching_result == 3:
                        return (isfloat, j)
                    
                
                break
        
        pattern_input : Tuple[bool, int] = loop(False, i)
        i_1 : int = pattern_input[1] or 0
        return (i_1, Json(1, parse_1(s[start:(i_1 - 1) + 1])) if (pattern_input[0]) else (Json(0, parse(s[start:(i_1 - 1) + 1], 511, False, 64))))
    
    return arrow_47


Parsec_Json_jNumber : Callable[[int, str], Tuple[int, Json]] = apply

def f(__unit: Any=None) -> bool:
    return True


Parsec_Json_jTrue : Callable[[int, str], Tuple[int, _B]] = Parsec_pMap(f, uncurry(2, Parsec_pStr_("true")))

def f(__unit: Any=None) -> bool:
    return True


Parsec_Json_jFalse : Callable[[int, str], Tuple[int, _B]] = Parsec_pMap(f, uncurry(2, Parsec_pStr_("false")))

Parsec_Json_jNull : Callable[[int, str], Tuple[int, None]] = Parsec_pStr_("null")

Parsec_Json_jStr : Callable[[int, str], Tuple[int, str]] = Parsec_pStr

Parsec_Json_refObject : FSharpRef[Callable[[int, str], Tuple[int, List[Tuple[str, Json]]]]] = FSharpRef(None)

Parsec_Json_jObject : Callable[[int, str], Tuple[int, _A]] = Parsec_pRef(Parsec_Json_refObject)

Parsec_Json_refList : FSharpRef[Callable[[int, str], Tuple[int, List[Json]]]] = FSharpRef(None)

Parsec_Json_jList : Callable[[int, str], Tuple[int, _A]] = Parsec_pRef(Parsec_Json_refList)

def arrow_49(_arg1: str) -> Callable[[int, str], Tuple[int, Json]]:
    if _arg1 == "-":
        return Parsec_Json_jNumber
    
    elif _arg1 == "[":
        def f(arg0: List[Json]) -> Json:
            return Json(5, arg0)
        
        return Parsec_pMap(f, uncurry(2, Parsec_Json_jList))
    
    elif _arg1 == "f":
        def f_3(arg0_3: bool) -> Json:
            return Json(2, arg0_3)
        
        return Parsec_pMap(f_3, uncurry(2, Parsec_Json_jFalse))
    
    elif _arg1 == "n":
        def f_4(__unit: Any=None) -> Json:
            return Json(4)
        
        return Parsec_pMap(f_4, uncurry(2, Parsec_Json_jNull))
    
    elif _arg1 == "t":
        def f_2(arg0_2: bool) -> Json:
            return Json(2, arg0_2)
        
        return Parsec_pMap(f_2, uncurry(2, Parsec_Json_jTrue))
    
    elif _arg1 == "{":
        def f_1(arg0_1: List[Tuple[str, Json]]) -> Json:
            return Json(6, arg0_1)
        
        return Parsec_pMap(f_1, uncurry(2, Parsec_Json_jObject))
    
    else: 
        def arrow_48(__unit: Any=None) -> bool:
            c : str = _arg1
            return c <= "9" if (c >= "0") else (False)
        
        if arrow_48():
            return Parsec_Json_jNumber
        
        elif _arg1 == "\"":
            def f_5(arg0_4: str) -> Json:
                return Json(3, arg0_4)
            
            return Parsec_pMap(f_5, uncurry(2, Parsec_Json_jStr))
        
        else: 
            raise Exception(_arg1)
        
    


Parsec_Json_json : Callable[[int, str], Tuple[int, _A]] = Parsec_la1(uncurry(3, arrow_49))

def arrow_51(i: int) -> Callable[[str], Tuple[int, List[Any]]]:
    def arrow_50(s: str) -> Tuple[int, List[Any]]:
        i_2 : int = Parsec_pSpc(Parsec_pChar_("{")(i)(s)[0])(s)[0] or 0
        if i_2 >= len(s):
            raise Exception("incomplete object")
        
        def each(i_3: int, s_1: str) -> Tuple[int, Tuple[str, Json]]:
            pattern_input_2 : Tuple[int, str] = Parsec_allowSPC(uncurry(2, Parsec_Json_jStr))(i_3)(s_1)
            pattern_input_3 : Tuple[int, None] = Parsec_allowSPC(uncurry(2, Parsec_pChar_(":")))(pattern_input_2[0])(s_1)
            pattern_input_4 : Tuple[int, Json] = Parsec_allowSPC(uncurry(2, Parsec_Json_json))(pattern_input_3[0])(s_1)
            return (pattern_input_4[0], (pattern_input_2[1], pattern_input_4[1]))
        
        return (i_2 + 1, []) if (s[i_2] == "}") else (Parsec_pSepRep(uncurry(2, Parsec_Json_pDictSep), each)(i_2)(s))
    
    return arrow_50


Parsec_Json_refObject.contents = arrow_51

def arrow_53(i: int) -> Callable[[str], Tuple[int, List[Any]]]:
    def arrow_52(s: str) -> Tuple[int, List[Any]]:
        i_2 : int = Parsec_pSpc(Parsec_pChar_("[")(i)(s)[0])(s)[0] or 0
        if i_2 >= len(s):
            raise Exception("incomplete list")
        
        return (i_2 + 1, []) if (s[i_2] == "]") else (Parsec_pSepRep(uncurry(2, Parsec_Json_pListSep), uncurry(2, Parsec_allowSPC(uncurry(2, Parsec_Json_json))))(i_2)(s))
    
    return arrow_52


Parsec_Json_refList.contents = arrow_53

def parse_json(s: str) -> Json:
    pattern_input : Tuple[int, Json] = Parsec_allowSPC(uncurry(2, Parsec_Json_json))(0)(s)
    if pattern_input[0] != len(s):
        raise Exception("json parse incomplete")
    
    else: 
        return pattern_input[1]
    


def int64from_json(_arg1: Json) -> Any:
    if _arg1.tag == 0:
        return _arg1.fields[0]
    
    else: 
        raise Exception("invalid conversion to int")
    


def double_from_json(_arg1: Json) -> float:
    if _arg1.tag == 1:
        return _arg1.fields[0]
    
    else: 
        raise Exception("invalid conversion to float")
    


def bool_from_json(_arg1: Json) -> bool:
    if _arg1.tag == 2:
        return _arg1.fields[0]
    
    else: 
        raise Exception("invalid conversion to bool")
    


def string_from_json(_arg1: Json) -> str:
    if _arg1.tag == 3:
        return _arg1.fields[0]
    
    else: 
        raise Exception("invalid conversion to bool")
    


def char_from_json(_arg1: Json) -> str:
    (pattern_matching_result,) = (None,)
    if _arg1.tag == 3:
        if len(_arg1.fields[0]) != 1:
            pattern_matching_result = 0
        
        else: 
            pattern_matching_result = 1
        
    
    else: 
        pattern_matching_result = 1
    
    if pattern_matching_result == 0:
        raise Exception("invalid interpretaion from string to char")
    
    elif pattern_matching_result == 1:
        if _arg1.tag == 3:
            return _arg1.fields[0][0]
        
        else: 
            raise Exception("invalid conversion to bool")
        
    


def unit_from_json(_arg1: Json) -> None:
    (pattern_matching_result,) = (None,)
    if _arg1.tag == 0:
        if equals(_arg1.fields[0], from_bits(0, 0, False)):
            pattern_matching_result = 0
        
        else: 
            pattern_matching_result = 1
        
    
    else: 
        pattern_matching_result = 1
    
    if pattern_matching_result == 0:
        pass
    
    elif pattern_matching_result == 1:
        raise Exception("invalid conversion to unit")
    


ADT_TAG : str = "_TAG"

ADT_VALS : str = "_VALUES"

def expr_54(gen0: TypeInfo) -> TypeInfo:
    return union_type("AJson.evidence`1", [gen0], evidence_1, lambda: [[]])


class evidence_1(Union, Generic[_A]):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["Evidence"]
    

evidence_1_reflection = expr_54

def obj_from_json(t: Any, data: Json) -> Any:
    if int8_type is t:
        return (int(to_int(int64from_json(data))) + 0x80 & 0xFF) - 0x80
    
    elif int16_type is t:
        return (int(to_int(int64from_json(data))) + 0x8000 & 0xFFFF) - 0x8000
    
    elif int32_type is t:
        return int(to_int(int64from_json(data)))
    
    elif class_type("System.Int64") is t:
        return int64from_json(data)
    
    elif float64_type is t:
        return double_from_json(data)
    
    elif float64_type is t:
        return double_from_json(data)
    
    elif class_type("System.Decimal") is t:
        return Decimal(double_from_json(data))
    
    elif bool_type is t:
        return bool_from_json(data)
    
    elif char_type is t:
        s : str = string_from_json(data)
        if len(s) != 1:
            raise Exception(to_text(interpolate("%P() to char", [s])))
        
        else: 
            return s[0]
        
    
    elif unit_type is t:
        value_10 : None = unit_from_json(data)
        return None
    
    elif string_type is t:
        return string_from_json(data)
    
    elif is_array(t):
        eltype : Any = get_element_type(t)
        seq_1 : List[Json]
        if data.tag == 5:
            seq_1 = data.fields[0]
        
        else: 
            raise Exception(to_text(interpolate("convert %P() to %P()", [Json__get_kind(data), t])))
        
        if eltype is int32_type:
            def arrow_55(i: int, t: Any=t, data: Json=data) -> int:
                return int(to_int(int64from_json(seq_1[i])))
            
            return initialize(len(seq_1), arrow_55, Int32Array)
        
        elif eltype == class_type("System.Int64"):
            def arrow_56(i_1: int, t: Any=t, data: Json=data) -> Any:
                return int64from_json(seq_1[i_1])
            
            return initialize(len(seq_1), arrow_56, None)
        
        elif eltype is int16_type:
            def arrow_57(i_2: int, t: Any=t, data: Json=data) -> int:
                return (int(to_int(int64from_json(seq_1[i_2]))) + 0x8000 & 0xFFFF) - 0x8000
            
            return initialize(len(seq_1), arrow_57, Int16Array)
        
        elif eltype is int8_type:
            def arrow_58(i_3: int, t: Any=t, data: Json=data) -> int:
                return (int(to_int(int64from_json(seq_1[i_3]))) + 0x80 & 0xFF) - 0x80
            
            return initialize(len(seq_1), arrow_58, Int8Array)
        
        elif eltype is uint32_type:
            def arrow_59(i_4: int, t: Any=t, data: Json=data) -> int:
                return int(to_int(int64from_json(seq_1[i_4]))+0x100000000 if to_int(int64from_json(seq_1[i_4])) < 0 else to_int(int64from_json(seq_1[i_4])))
            
            return initialize(len(seq_1), arrow_59, Uint32Array)
        
        elif eltype == class_type("System.UInt64"):
            def arrow_60(i_5: int, t: Any=t, data: Json=data) -> Any:
                return from_value(int64from_json(seq_1[i_5]), True)
            
            return initialize(len(seq_1), arrow_60, None)
        
        elif eltype is uint8_type:
            def arrow_61(i_6: int, t: Any=t, data: Json=data) -> int:
                return int(to_int(int64from_json(seq_1[i_6]))+0x100 if to_int(int64from_json(seq_1[i_6])) < 0 else to_int(int64from_json(seq_1[i_6]))) & 0xFF
            
            return initialize(len(seq_1), arrow_61, Uint8Array)
        
        elif eltype is uint16_type:
            def arrow_62(i_7: int, t: Any=t, data: Json=data) -> int:
                return int(to_int(int64from_json(seq_1[i_7]))+0x10000 if to_int(int64from_json(seq_1[i_7])) < 0 else to_int(int64from_json(seq_1[i_7]))) & 0xFFFF
            
            return initialize(len(seq_1), arrow_62, Uint16Array)
        
        elif eltype is float64_type:
            def arrow_63(i_8: int, t: Any=t, data: Json=data) -> float:
                return double_from_json(seq_1[i_8])
            
            return initialize(len(seq_1), arrow_63, Float64Array)
        
        elif eltype is float64_type:
            def arrow_64(i_9: int, t: Any=t, data: Json=data) -> float:
                return double_from_json(seq_1[i_9])
            
            return initialize(len(seq_1), arrow_64, Float64Array)
        
        elif eltype == class_type("System.Decimal"):
            def arrow_65(i_10: int, t: Any=t, data: Json=data) -> Any:
                return Decimal(double_from_json(seq_1[i_10]))
            
            return initialize(len(seq_1), arrow_65, None)
        
        elif eltype is string_type:
            def arrow_66(i_11: int, t: Any=t, data: Json=data) -> str:
                return string_from_json(seq_1[i_11])
            
            return initialize(len(seq_1), arrow_66, None)
        
        elif eltype is bool_type:
            def arrow_67(i_12: int, t: Any=t, data: Json=data) -> bool:
                return bool_from_json(seq_1[i_12])
            
            return initialize(len(seq_1), arrow_67, None)
        
        elif eltype is unit_type:
            def arrow_68(i_13: int, t: Any=t, data: Json=data) -> None:
                unit_from_json(seq_1[i_13])
            
            return initialize(len(seq_1), arrow_68, None)
        
        elif eltype is char_type:
            def arrow_69(i_14: int, t: Any=t, data: Json=data) -> str:
                return char_from_json(seq_1[i_14])
            
            return initialize(len(seq_1), arrow_69, None)
        
        else: 
            def arrow_70(i_15: int, t: Any=t, data: Json=data) -> Any:
                return obj_from_json(eltype, seq_1[i_15])
            
            return initialize(len(seq_1), arrow_70, None)
        
    
    elif equals_1(get_generic_type_definition(t), option_type(obj_type)) if (is_generic_type(t)) else (False):
        if data.tag == 4:
            return None
        
        else: 
            return some(obj_from_json(get_generics(t)[0], data))
        
    
    elif equals_1(get_generic_type_definition(t), list_type(obj_type)) if (is_generic_type(t)) else (False):
        o : FSharpList[Any] = empty()
        seq_3 : List[Json]
        if data.tag == 5:
            seq_3 = data.fields[0]
        
        else: 
            raise Exception(to_text(interpolate("convert %P() to %P()", [Json__get_kind(data), t])))
        
        for i_16 in range(len(seq_3) - 1, 0 - 1, -1):
            o = cons(obj_from_json(get_generics(t)[0], seq_3[i_16]), o)
        return o
    
    elif is_record(t):
        def mapping(f: Any, t: Any=t, data: Json=data) -> Tuple[str, Any]:
            return (name(f), f[1])
        
        fields : List[Tuple[str, Any]] = map(mapping, get_record_elements(t), None)
        arguments : List[Any] = fill([0] * len(fields), 0, len(fields), None)
        def arrow_71(t: Any=t, data: Json=data) -> List[Tuple[str, Json]]:
            raise Exception(to_text(interpolate("convert %P() to %P()", [Json__get_kind(data), t])))
        
        enumerator : Any = get_enumerator(data.fields[0] if (data.tag == 6) else (arrow_71()))
        try: 
            while enumerator.System_Collections_IEnumerator_MoveNext():
                for_loop_var : Tuple[str, Json] = enumerator.System_Collections_Generic_IEnumerator_00601_get_Current()
                def arrow_72(tupled_arg: Tuple[str, Any]) -> bool:
                    return for_loop_var[0] == tupled_arg[0]
                
                i_17 : int = find_index(arrow_72, fields) or 0
                pattern_input : Tuple[str, Any] = fields[i_17]
                arguments[i_17] = obj_from_json(pattern_input[1], for_loop_var[1])
        
        finally: 
            dispose(enumerator)
        
        return make_record(t, arguments)
    
    elif is_tuple(t):
        eltypes : List[Any] = get_tuple_elements(t)
        seq_5 : List[Json]
        if data.tag == 5:
            seq_5 = data.fields[0]
        
        else: 
            raise Exception(to_text(interpolate("convert %P() to %P()", [Json__get_kind(data), t])))
        
        def arrow_73(i_18: int, t: Any=t, data: Json=data) -> Any:
            return obj_from_json(eltypes[i_18], seq_5[i_18])
        
        return make_tuple(initialize(len(seq_5), arrow_73, None), t)
    
    elif is_union(t):
        pairs_3 : List[Tuple[str, Json]]
        if data.tag == 6:
            pairs_3 = data.fields[0]
        
        else: 
            raise Exception(to_text(interpolate("convert %P() to %P()", [Json__get_kind(data), t])))
        
        def arrow_74(tupled_arg_1: Tuple[str, Json], t: Any=t, data: Json=data) -> bool:
            return tupled_arg_1[0] == ADT_TAG
        
        tag_1 : str = string_from_json(find(arrow_74, pairs_3)[1])
        def arrow_75(tupled_arg_2: Tuple[str, Json], t: Any=t, data: Json=data) -> bool:
            return tupled_arg_2[0] == ADT_VALS
        
        values : Json = find(arrow_75, pairs_3)[1]
        def predicate(case: Any, t: Any=t, data: Json=data) -> bool:
            return name(case) == tag_1
        
        case_1 : Any = find_1(predicate, get_union_cases(t))
        def mapping_1(f_1: Any, t: Any=t, data: Json=data) -> Any:
            return f_1[1]
        
        fieldtypes : List[Any] = map(mapping_1, get_union_case_fields(case_1), None)
        def arrow_77(t: Any=t, data: Json=data) -> List[Any]:
            values_1 : List[Json] = values.fields[0]
            def arrow_76(i_19: int) -> Any:
                return obj_from_json(fieldtypes[i_19], values_1[i_19])
            
            return initialize(len(values_1), arrow_76, None)
        
        def arrow_78(t: Any=t, data: Json=data) -> List[Any]:
            raise Exception(to_text(interpolate("convert %P() to %P()", [Json__get_kind(data), t])))
        
        return make_union(case_1, arrow_77() if (values.tag == 5) else (arrow_78()))
    
    else: 
        raise Exception(to_text(interpolate("unsupported data type fromJson: %P()", [t])))
    


def obj_to_json(t_mut: Any, o_mut: Any) -> Json:
    while True:
        (t, o) = (t_mut, o_mut)
        if int8_type is t:
            return Json(0, from_integer(o, False, 0))
        
        elif int16_type is t:
            return Json(0, from_integer(o, False, 1))
        
        elif int32_type is t:
            return Json(0, from_integer(o, False, 2))
        
        elif class_type("System.Int64") is t:
            return Json(0, o)
        
        elif float64_type is t:
            return Json(1, o)
        
        elif float64_type is t:
            return Json(1, o)
        
        elif class_type("System.Decimal") is t:
            return Json(1, to_number(o))
        
        elif bool_type is t:
            return Json(2, o)
        
        elif char_type is t:
            return Json(3, o)
        
        elif unit_type is t:
            return Json(0, from_integer(0, False, 2))
        
        elif string_type is t:
            return Json(3, o)
        
        elif is_array(t):
            eltype : Any = get_element_type(t)
            if eltype is int32_type:
                def mapping(it: int, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it)
                
                return Json(5, list(map(mapping, o, None)))
            
            elif eltype == class_type("System.Int64"):
                def mapping_1(it_1: Any, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_1)
                
                return Json(5, list(map(mapping_1, o, None)))
            
            elif eltype is int16_type:
                def mapping_2(it_2: int, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_2)
                
                return Json(5, list(map(mapping_2, o, None)))
            
            elif eltype is int8_type:
                def mapping_3(it_3: int, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_3)
                
                return Json(5, list(map(mapping_3, o, None)))
            
            elif eltype is uint32_type:
                def mapping_4(it_4: int, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_4)
                
                return Json(5, list(map(mapping_4, o, None)))
            
            elif eltype == class_type("System.UInt64"):
                def mapping_5(it_5: Any, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_5)
                
                return Json(5, list(map(mapping_5, o, None)))
            
            elif eltype is uint8_type:
                def mapping_6(it_6: int, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_6)
                
                return Json(5, list(map(mapping_6, o, None)))
            
            elif eltype is uint16_type:
                def mapping_7(it_7: int, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_7)
                
                return Json(5, list(map(mapping_7, o, None)))
            
            elif eltype is float64_type:
                def mapping_8(it_8: float, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_8)
                
                return Json(5, list(map(mapping_8, o, None)))
            
            elif eltype is float64_type:
                def mapping_9(it_9: float, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_9)
                
                return Json(5, list(map(mapping_9, o, None)))
            
            elif eltype == class_type("System.Decimal"):
                def mapping_10(it_10: Any, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_10)
                
                return Json(5, list(map(mapping_10, o, None)))
            
            elif eltype is string_type:
                def mapping_11(it_11: str, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_11)
                
                return Json(5, list(map(mapping_11, o, None)))
            
            elif eltype is bool_type:
                def mapping_12(it_12: bool, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_12)
                
                return Json(5, list(map(mapping_12, o, None)))
            
            elif eltype is unit_type:
                def mapping_13(t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, None)
                
                return Json(5, list(map(mapping_13, o, None)))
            
            elif eltype is char_type:
                def mapping_14(it_14: str, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_14)
                
                return Json(5, list(map(mapping_14, o, None)))
            
            else: 
                def mapping_15(it_15: Any, t: Any=t, o: Any=o) -> Json:
                    return obj_to_json(eltype, it_15)
                
                return Json(5, list(map(mapping_15, o, None)))
            
        
        elif equals_1(get_generic_type_definition(t), option_type(obj_type)) if (is_generic_type(t)) else (False):
            eltype_1 : Any = get_generics(t)[0]
            match_value : Optional[Any] = o
            if match_value is not None:
                t_mut = eltype_1
                o_mut = value_29(match_value)
                continue
            
            else: 
                return Json(4)
            
        
        elif equals_1(get_generic_type_definition(t), list_type(obj_type)) if (is_generic_type(t)) else (False):
            eltype_2 : Any = get_generics(t)[0]
            def mapping_16(it_16: Any, t: Any=t, o: Any=o) -> Json:
                return obj_to_json(eltype_2, it_16)
            
            return Json(5, list(map_1(mapping_16, o)))
        
        elif is_record(t):
            def mapping_17(f: Any, t: Any=t, o: Any=o) -> Tuple[str, Json]:
                return (name(f), obj_to_json(f[1], get_record_field(o, f)))
            
            return Json(6, list(map(mapping_17, get_record_elements(t), None)))
        
        elif is_tuple(t):
            eltypes : List[Any] = get_tuple_elements(t)
            def mapping_18(i_1: int, e: Any, t: Any=t, o: Any=o) -> Json:
                return obj_to_json(eltypes[i_1], e)
            
            return Json(5, list(map_indexed(mapping_18, get_tuple_fields(o), None)))
        
        elif is_union(t):
            pattern_input : Tuple[Any, List[Any]] = get_union_fields(o, t)
            case : Any = pattern_input[0]
            def mapping_19(f_1: Any, t: Any=t, o: Any=o) -> Any:
                return f_1[1]
            
            fieldtypes : List[Any] = map(mapping_19, get_union_case_fields(case), None)
            def mapping_20(i_2: int, e_1: Any, t: Any=t, o: Any=o) -> Json:
                return obj_to_json(fieldtypes[i_2], e_1)
            
            return Json(6, list([(ADT_TAG, Json(3, name(case))), (ADT_VALS, Json(5, list(map_indexed(mapping_20, pattern_input[1], None))))]))
        
        else: 
            raise Exception(to_text(interpolate("unsupported data type fromJson: %P()", [t])))
        
        break


def escape_string(s: str) -> str:
    buf : Any = StringBuilder__ctor_Z524259A4(len(s))
    for i in range(0, (len(s) - 1) + 1, 1):
        def arrow_79(s: str=s) -> Any:
            c : str = s[i]
            return StringBuilder__Append_Z721C83C5(buf, "\\b") if (c == "\b") else (StringBuilder__Append_Z721C83C5(buf, "\\t") if (c == "\t") else (StringBuilder__Append_Z721C83C5(buf, "\\n") if (c == "\n") else (StringBuilder__Append_Z721C83C5(buf, "\\f") if (c == "\f") else (StringBuilder__Append_Z721C83C5(buf, "\\r") if (c == "\r") else (StringBuilder__Append_Z721C83C5(buf, "\\\"") if (c == "\"") else (StringBuilder__Append_Z721C83C5(buf, "\\\\") if (c == "\\") else (StringBuilder__Append_244C7CD6(buf, c))))))))
        
        ignore(arrow_79())
    return to_string(buf)


def serialize_json(x: Json) -> str:
    if x.tag == 1:
        return to_string(x.fields[0])
    
    elif x.tag == 2:
        if x.fields[0]:
            return "true"
        
        else: 
            return "false"
        
    
    elif x.tag == 3:
        return ("\"" + escape_string(x.fields[0])) + "\""
    
    elif x.tag == 4:
        return "null"
    
    elif x.tag == 5:
        def arrow_80(x_1: Json, x: Json=x) -> str:
            return serialize_json(x_1)
        
        return ("[" + join(",", map_2(arrow_80, x.fields[0]))) + "]"
    
    elif x.tag == 6:
        def arrow_81(tupled_arg: Tuple[str, Json], x: Json=x) -> str:
            return ((("\"" + escape_string(tupled_arg[0])) + "\"") + ":") + serialize_json(tupled_arg[1])
        
        return ("{" + join(",", map_2(arrow_81, x.fields[0]))) + "}"
    
    else: 
        return int64_to_string(x.fields[0])
    


