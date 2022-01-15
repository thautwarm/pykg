from __future__ import annotations
from _fable_pykg_infr import (solve_deps, TupleCons, create_tuple, ge_tuple, le_tuple, get_major, get_minor, get_micro)
from typing import (List, Optional, Tuple, Any)
from z3 import (ModelRef, AstRef, Or, simplify)
from ..fable_modules.fable_library.option import map
from ..fable_modules.fable_library.reflection import (TypeInfo, class_type)
from ..fable_modules.fable_library.string import (to_console, printf)

def expr_17() -> TypeInfo:
    return class_type("FablePykg.Z3.z3Model", None, z3Model)


class z3Model:
    def __init__(self, m: ModelRef) -> None:
        self.m = m
    

z3Model_reflection = expr_17

def z3model__ctor_D649C1C(m: ModelRef) -> z3Model:
    return z3Model(m)


def solve(a: List[AstRef[bool]]) -> Optional[z3Model]:
    def arrow_18(m: ModelRef, a: List[AstRef[bool]]=a) -> z3Model:
        return z3model__ctor_D649C1C(m)
    
    return map(arrow_18, solve_deps(a))


def const_ver(major: int, minor: int, micro: int) -> AstRef[Tuple[int, int, int]]:
    return TupleCons(major, minor, micro)


def test() -> None:
    v : AstRef[Tuple[int, int, int]] = create_tuple("m")
    def arrow_20(__unit: Any=None) -> AstRef[bool]:
        arg1_2 : AstRef[bool]
        arg1_4 : AstRef[Tuple[int, int, int]] = const_ver(1, 2, 9)
        arg1_2 = v == arg1_4
        def arrow_19(__unit: Any=None) -> AstRef[bool]:
            arg1_3 : AstRef[Tuple[int, int, int]] = const_ver(1, 2, 6)
            return v == arg1_3
        
        return Or(arrow_19(), arg1_2)
    
    model : Optional[z3Model] = solve([ge_tuple(v, const_ver(1, 2, 3)), le_tuple(v, const_ver(1, 2, 8)), arrow_20()])
    if model is not None:
        model_1 : z3Model = model
        tupled_arg : Tuple[int, int, int]
        x : AstRef[Tuple[int, int, int]] = model_1.m[v]
        def arrow_21(__unit: Any=None) -> int:
            a_2 : AstRef[int] = simplify(get_major(x))
            return a_2.as_long()
        
        def arrow_22(__unit: Any=None) -> int:
            a_4 : AstRef[int] = simplify(get_minor(x))
            return a_4.as_long()
        
        def arrow_23(__unit: Any=None) -> int:
            a_6 : AstRef[int] = simplify(get_micro(x))
            return a_6.as_long()
        
        tupled_arg = (arrow_21(), arrow_22(), arrow_23())
        to_console(printf("%A"))((tupled_arg[0], tupled_arg[1], tupled_arg[2]))
    
    else: 
        raise Exception("solution failed")
    


