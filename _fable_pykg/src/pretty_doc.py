from __future__ import annotations
from array import array
from typing import (Any, List, TypeVar, Optional, Generic, Callable)
from ..fable_modules.fable_library.array import (take, concat as concat_1, append, last, head, skip, equals_with)
from ..fable_modules.fable_library.list import (empty as empty_1, cons, FSharpList, is_empty, tail, head as head_1)
from ..fable_modules.fable_library.reflection import (TypeInfo, list_type, int32_type, string_type, union_type, class_type, record_type)
from ..fable_modules.fable_library.seq import (map, to_list)
from ..fable_modules.fable_library.string import replicate
from ..fable_modules.fable_library.system_text import (StringBuilder__ctor, StringBuilder__Append_Z721C83C5)
from ..fable_modules.fable_library.types import (Union, Record, to_string)
from ..fable_modules.fable_library.util import (equals, IEnumerable, ignore, get_enumerator)

__A = TypeVar("__A")

_A = TypeVar("_A")

def expr_0() -> TypeInfo:
    return union_type("FablePykg.PrettyDoc.Doc", [], Doc, lambda: [[["Item1", Doc_reflection()], ["Item2", Doc_reflection()]], [["Item", list_type(Doc_reflection())]], [["Item", Doc_reflection()]], [["Item1", int32_type], ["Item2", Doc_reflection()]], [["Item", string_type]], [["Item", Doc_reflection()]]])


class Doc(Union):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["Concat", "VSep", "Align", "Indent", "LineSeg", "Breakable"]
    

Doc_reflection = expr_0

def Doc_op_Multiply_Z32C4A9C0(a: Doc, b: Doc) -> Doc:
    return Doc(0, a, b)


def Doc_op_Addition_Z32C4A9C0(a: Doc, b: Doc) -> Doc:
    return Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(a, Doc(4, " ")), b)


def Doc_op_RightShift_Z295EA572(a: Doc, b: int) -> Doc:
    return Doc(3, b, a)


def expr_1() -> TypeInfo:
    return union_type("FablePykg.PrettyDoc.DocPrimitive", [], DocPrimitive, lambda: [[], [], [["Item", int32_type]], [["Item", string_type]], []])


class DocPrimitive(Union):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["DP_PopIndent", "DP_PushCurrentIndent", "DP_PushIndent", "DP_Word", "DP_Breakable"]
    

DocPrimitive_reflection = expr_1

def Array_drop(i: int, arr: List[__A]) -> List[__A]:
    return take(len(arr) - i, arr, None)


def compile_to_prims(doc: Doc) -> List[List[DocPrimitive]]:
    if doc.tag == 0:
        l_1 : List[List[DocPrimitive]] = compile_to_prims(doc.fields[0])
        r_1 : List[List[DocPrimitive]] = compile_to_prims(doc.fields[1])
        if len(l_1) == 0:
            return r_1
        
        elif len(r_1) == 0:
            return l_1
        
        else: 
            return concat_1([Array_drop(1, l_1), [append(last(l_1), head(r_1), None)], skip(1, r_1, None)], None)
        
    
    elif doc.tag == 2:
        it : List[List[DocPrimitive]] = compile_to_prims(doc.fields[0])
        if len(it) == 0:
            return it
        
        else: 
            it[0] = append([DocPrimitive(1)], it[0], None)
            it[len(it) - 1] = append(it[len(it) - 1], [DocPrimitive(0)], None)
            return it
        
    
    elif doc.tag == 3:
        prefix : List[DocPrimitive] = [DocPrimitive(2, doc.fields[0])]
        it_1 : List[List[DocPrimitive]] = compile_to_prims(doc.fields[1])
        if len(it_1) == 0:
            return it_1
        
        else: 
            it_1[0] = append(prefix, it_1[0], None)
            it_1[len(it_1) - 1] = append(it_1[len(it_1) - 1], [DocPrimitive(0)], None)
            return it_1
        
    
    elif doc.tag == 1:
        def arrow_2(doc_2: Doc, doc: Doc=doc) -> List[List[DocPrimitive]]:
            return compile_to_prims(doc_2)
        
        return concat_1(map(arrow_2, doc.fields[0]), None)
    
    elif doc.tag == 4:
        return [[DocPrimitive(3, doc.fields[0])]]
    
    else: 
        match_value : List[List[DocPrimitive]] = compile_to_prims(doc.fields[0])
        def arrow_4(x: List[DocPrimitive], y: List[DocPrimitive], doc: Doc=doc) -> bool:
            def arrow_3(x_1: DocPrimitive, y_1: DocPrimitive) -> bool:
                return equals(x_1, y_1)
            
            return equals_with(arrow_3, x, y)
        
        if len(match_value) == 0 if (not equals_with(arrow_4, match_value, None)) else (False):
            return [[DocPrimitive(4)]]
        
        else: 
            many : List[List[DocPrimitive]] = match_value
            if len(many[0]) == 0:
                return [[DocPrimitive(4)]]
            
            else: 
                many[0] = append([DocPrimitive(4)], many[0], None)
                return many
            
        
    


def expr_5(gen0: TypeInfo) -> TypeInfo:
    return class_type("FablePykg.PrettyDoc.Stack`1", [gen0], Stack_1)


class Stack_1(Generic[_A]):
    def __init__(self, init: Optional[IEnumerable[_A]]=None) -> None:
        self._content = to_list(init) if (init is not None) else (empty_1())
    

Stack_1_reflection = expr_5

def Stack_1__ctor_Z5E7FEA67(init: Optional[IEnumerable[_A]]=None) -> Stack_1[_A]:
    return Stack_1(init)


def Stack_1__Push_2B595(__: Stack_1[_A], a: _A=None) -> None:
    __._content = cons(a, __._content)


def Stack_1__Pop(__: Stack_1[_A]) -> _A:
    match_value : FSharpList[_A] = __._content
    if not is_empty(match_value):
        __._content = tail(match_value)
        return head_1(match_value)
    
    else: 
        raise Exception("negative stacksize")
    


def Stack_1__get_Last(__: Stack_1[_A]) -> _A:
    match_value : FSharpList[_A] = __._content
    if not is_empty(match_value):
        return head_1(match_value)
    
    else: 
        raise Exception("negative stacksize")
    


def expr_6() -> TypeInfo:
    return record_type("FablePykg.PrettyDoc.render_options", [], render_options, lambda: [["expected_line_width", int32_type]])


class render_options(Record):
    def __init__(self, expected_line_width: int=None) -> None:
        super().__init__()
        self.expected_line_width = expected_line_width or 0
    

render_options_reflection = expr_6

default_render_options : render_options = render_options(40)

def render(opts: render_options, setences: List[List[DocPrimitive]], write: Callable[[str], None]) -> None:
    levels : Stack_1[int] = Stack_1__ctor_Z5E7FEA67(array("i", [0]))
    if len(setences) == 0:
        pass
    
    else: 
        for idx in range(0, (len(setences) - 1) + 1, 1):
            words : List[DocPrimitive] = setences[idx]
            col : int = 0
            initialized : bool = False
            for idx_1 in range(0, (len(words) - 1) + 1, 1):
                word : DocPrimitive = words[idx_1]
                (pattern_matching_result,) = (None,)
                if word.tag == 4:
                    if col > opts.expected_line_width:
                        pattern_matching_result = 0
                    
                    else: 
                        pattern_matching_result = 1
                    
                
                else: 
                    pattern_matching_result = 1
                
                if pattern_matching_result == 0:
                    initialized = False
                    write("\n")
                
                elif pattern_matching_result == 1:
                    if word.tag == 3:
                        s : str = word.fields[0]
                        if not initialized:
                            col = (Stack_1__get_Last(levels) + col) or 0
                            write(replicate(col, " "))
                            initialized = True
                        
                        write(s)
                        col = (col + len(s)) or 0
                    
                    elif word.tag == 1:
                        Stack_1__Push_2B595(levels, col)
                    
                    elif word.tag == 0:
                        ignore(Stack_1__Pop(levels))
                    
                    elif word.tag == 2:
                        Stack_1__Push_2B595(levels, Stack_1__get_Last(levels) + word.fields[0])
                    
                
            write("\n")
    


def pretty(s: Any=None) -> Doc:
    def arrow_11(s: __A=s) -> str:
        copy_of_struct : __A = s
        return to_string(copy_of_struct)
    
    return Doc(4, arrow_11())


def seg(s: str) -> Doc:
    return Doc(4, s)


def vsep(lines: FSharpList[Doc]) -> Doc:
    return Doc(1, lines)


def align(seg_1: Doc) -> Doc:
    return Doc(2, seg_1)


def indent(i: int, x: Doc) -> Doc:
    return Doc(3, i, x)


def concat(a: Doc, b: Doc) -> Doc:
    return Doc(0, a, b)


empty : Doc = seg("")

def parens(a: Doc) -> Doc:
    return Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(seg("("), a), seg(")"))


def bracket(a: Doc) -> Doc:
    return Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(seg("["), a), seg("]"))


def brace(a: Doc) -> Doc:
    return Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(seg("{"), a), seg("}"))


space : Doc = seg(" ")

comma : Doc = seg(",")

def listof(lst: FSharpList[Doc]) -> Doc:
    if not is_empty(lst):
        res : Doc = head_1(lst)
        with get_enumerator(tail(lst)) as enumerator:
            while enumerator.System_Collections_IEnumerator_MoveNext():
                each : Doc = enumerator.System_Collections_Generic_IEnumerator_00601_get_Current()
                res = Doc_op_Multiply_Z32C4A9C0(res, each)
        return res
    
    else: 
        return empty
    


def seplist(sep: Doc, lst: FSharpList[Doc]) -> Doc:
    if not is_empty(lst):
        res : Doc = head_1(lst)
        with get_enumerator(tail(lst)) as enumerator:
            while enumerator.System_Collections_IEnumerator_MoveNext():
                each : Doc = enumerator.System_Collections_Generic_IEnumerator_00601_get_Current()
                res = Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(res, sep), each)
        return res
    
    else: 
        return empty
    


def arrayof(arr: List[Doc]) -> Doc:
    if len(arr) == 0:
        return empty
    
    else: 
        i : int = 1
        res : Doc = arr[0]
        while i < len(arr):
            res = Doc_op_Multiply_Z32C4A9C0(res, arr[i])
            i = (i + 1) or 0
        return res
    


def separray(sep: Doc, arr: List[Doc]) -> Doc:
    if len(arr) == 0:
        return empty
    
    else: 
        i : int = 1
        res : Doc = arr[0]
        while i < len(arr):
            res = Doc_op_Multiply_Z32C4A9C0(Doc_op_Multiply_Z32C4A9C0(res, sep), arr[i])
            i = (i + 1) or 0
        return res
    


def show_doc(opts: render_options, doc: Doc) -> str:
    sb : Any = StringBuilder__ctor()
    def arrow_13(x: str, opts: render_options=opts, doc: Doc=doc) -> None:
        ignore(StringBuilder__Append_Z721C83C5(sb, x))
    
    render(opts, compile_to_prims(doc), arrow_13)
    return to_string(sb)


def gen_doc(opts: render_options, doc: Doc, write: Callable[[str], None]) -> None:
    render(opts, compile_to_prims(doc), write)


