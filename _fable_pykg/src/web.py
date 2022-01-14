from __future__ import annotations
from typing import (Generic, List, TypeVar)
from .comp import commented_1
from .proj import (project, dep)

_A = TypeVar("_A")

class async_1(Generic[_A]):
    pass

def find_all_deps(proj: project) -> None:
    arr : List[commented_1[dep]] = proj.deps
    for idx in range(0, (len(arr) - 1) + 1, 1):
        if arr[idx].fields[1].tag == 0:
            raise Exception("")
        
        else: 
            raise Exception("Match failure")
        
        raise Exception("")


