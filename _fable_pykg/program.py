from typing import (TypeVar, Any)
from .fable_modules.fable_library.map import (empty, try_find, add)
from .fable_modules.fable_library.option import Option
from .fable_modules.fable_library.string import (to_console, printf)
from .fable_modules.fable_library.util import compare

__A = TypeVar("__A")

def d() -> Any:
    class ObjectExpr35:
        @property
        def Compare(self) -> Any:
            def arrow_34(x: __A, y: __A=None) -> int:
                return compare(x, y)
            
            return arrow_34
        
    return empty(ObjectExpr35())


match_value : Option[int] = try_find("asda", add("asda", 1, d()))


if match_value is not None:
    v : int = match_value or 0
    to_console(printf("%A"))(v)

else: 
    raise Exception("Match failure")


