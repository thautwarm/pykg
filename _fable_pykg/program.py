from __future__ import annotations
from _fable_pykg_infr import parse
from typing import Any
from .fable_modules.fable_library.string import (to_console, printf)
from .src.comp import (serialize_comp, obj_to_comp, Component, obj_from_comp)
from .src.pretty_doc import (show_doc, default_render_options)
from .src.proj import (project_reflection, metadata_reflection)

def test_load_proj(comfig_string: str) -> None:
    def arrow_14(o: Any=None, comfig_string: str=comfig_string) -> Component:
        return obj_to_comp(project_reflection(), o)
    
    arg10 : str = show_doc(default_render_options, serialize_comp(arrow_14(obj_from_comp(project_reflection(), parse(comfig_string)))))
    to_console(printf("%s"))(arg10)


def test_load_meta(comfig_string: str) -> None:
    def arrow_15(o: Any=None, comfig_string: str=comfig_string) -> Component:
        return obj_to_comp(metadata_reflection(), o)
    
    arg10 : str = show_doc(default_render_options, serialize_comp(arrow_15(obj_from_comp(metadata_reflection(), parse(comfig_string)))))
    to_console(printf("%s"))(arg10)


