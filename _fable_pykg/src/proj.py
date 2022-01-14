from __future__ import annotations
from _fable_pykg_infr import parse
from typing import (Any, List)
from ..fable_modules.fable_library.option import Option
from ..fable_modules.fable_library.reflection import (TypeInfo, string_type, array_type, union_type, option_type, record_type)
from ..fable_modules.fable_library.types import (Union, Record)
from .comp import (specifier_reflection, commented_1_reflection, Component_reflection, commented_1, version, lift_array_1, lift_array_1_reflection, version_reflection, obj_from_comp)

def expr_3() -> TypeInfo:
    return union_type("FablePykg.Proj.dep", [], dep, lambda: [[["repo", string_type], ["version", commented_1_reflection(array_type(specifier_reflection()))]], [["path", string_type], ["version", commented_1_reflection(array_type(specifier_reflection()))]], [["name", string_type], ["version", commented_1_reflection(array_type(specifier_reflection()))], ["_unused", array_type(Component_reflection())]]])


class dep(Union):
    def __init__(self, tag: int, *fields: Any) -> None:
        super().__init__()
        self.tag : int = tag or 0
        self.fields : List[Any] = list(fields)
    
    @staticmethod
    def cases() -> List[str]:
        return ["GitHub", "Local", "PyPI"]
    

dep_reflection = expr_3

def expr_6() -> TypeInfo:
    return record_type("FablePykg.Proj.author", [], author, lambda: [["name", string_type], ["email", option_type(string_type)]])


class author(Record):
    def __init__(self, name: str, email: Option[str]) -> None:
        super().__init__()
        self.name = name
        self.email = email
    

author_reflection = expr_6

def expr_7() -> TypeInfo:
    return record_type("FablePykg.Proj.project", [], project, lambda: [["name", commented_1_reflection(string_type)], ["authors", lift_array_1_reflection(author_reflection())], ["version", commented_1_reflection(version_reflection())], ["deps", array_type(commented_1_reflection(dep_reflection()))], ["src", array_type(string_type)]])


class project(Record):
    def __init__(self, name: commented_1[str], authors: lift_array_1[author], version: commented_1[version], deps: List[commented_1[dep]], src: List[str]) -> None:
        super().__init__()
        self.name = name
        self.authors = authors
        self.version = version
        self.deps = deps
        self.src = src
    

project_reflection = expr_7

def parse_project(s: str) -> project:
    return obj_from_comp(project_reflection(), parse(s))


