from __future__ import annotations
from _fable_pykg_infr import (Version, parse)
from typing import (List, Optional, Any)
from ..fable_modules.fable_library.reflection import (TypeInfo, string_type, array_type, record_type, option_type, class_type)
from ..fable_modules.fable_library.types import Record
from .comp import (commented_1, specifier, specifier_reflection, commented_1_reflection, lift_array_1, lift_array_1_reflection, obj_from_comp, serialize_comp, obj_to_comp, Component)
from .pretty_doc import (show_doc, default_render_options)

def expr_7() -> TypeInfo:
    return record_type("FablePykg.Proj.dep", [], dep, lambda: [["name", string_type], ["version", commented_1_reflection(array_type(specifier_reflection()))]])


class dep(Record):
    def __init__(self, name: str, version: commented_1[List[specifier]]) -> None:
        super().__init__()
        self.name = name
        self.version = version
    

dep_reflection = expr_7

def expr_8() -> TypeInfo:
    return record_type("FablePykg.Proj.author", [], author, lambda: [["name", string_type], ["email", option_type(string_type)]])


class author(Record):
    def __init__(self, name: str, email: Optional[str]) -> None:
        super().__init__()
        self.name = name
        self.email = email
    

author_reflection = expr_8

def expr_9() -> TypeInfo:
    return record_type("FablePykg.Proj.project", [], project, lambda: [["name", commented_1_reflection(string_type)], ["mirror", commented_1_reflection(string_type)], ["builder", commented_1_reflection(string_type)], ["authors", lift_array_1_reflection(commented_1_reflection(author_reflection()))], ["version", commented_1_reflection(class_type("FablePykg.Comp.version"))], ["deps", lift_array_1_reflection(commented_1_reflection(dep_reflection()))], ["src", array_type(string_type)]])


class project(Record):
    def __init__(self, name: commented_1[str], mirror: commented_1[str], builder: commented_1[str], authors: lift_array_1[commented_1[author]], version: commented_1[Version], deps: lift_array_1[commented_1[dep]], src: List[str]) -> None:
        super().__init__()
        self.name = name
        self.mirror = mirror
        self.builder = builder
        self.authors = authors
        self.version = version
        self.deps = deps
        self.src = src
    

project_reflection = expr_9

def expr_10() -> TypeInfo:
    return record_type("FablePykg.Proj.dist", [], dist, lambda: [["version", commented_1_reflection(class_type("FablePykg.Comp.version"))], ["url", option_type(commented_1_reflection(string_type))], ["deps", lift_array_1_reflection(commented_1_reflection(dep_reflection()))]])


class dist(Record):
    def __init__(self, version: commented_1[Version], url: Optional[commented_1[str]], deps: lift_array_1[commented_1[dep]]) -> None:
        super().__init__()
        self.version = version
        self.url = url
        self.deps = deps
    

dist_reflection = expr_10

def expr_11() -> TypeInfo:
    return record_type("FablePykg.Proj.metadata", [], metadata, lambda: [["name", commented_1_reflection(string_type)], ["authors", lift_array_1_reflection(commented_1_reflection(author_reflection()))], ["distributions", lift_array_1_reflection(commented_1_reflection(dist_reflection()))]])


class metadata(Record):
    def __init__(self, name: commented_1[str], authors: lift_array_1[commented_1[author]], distributions: lift_array_1[commented_1[dist]]) -> None:
        super().__init__()
        self.name = name
        self.authors = authors
        self.distributions = distributions
    

metadata_reflection = expr_11

def parse_project(s: str) -> project:
    return obj_from_comp(project_reflection(), parse(s))


def parse_metadata(s: str) -> metadata:
    return obj_from_comp(metadata_reflection(), parse(s))


def serialize_dep(d: dep) -> str:
    def arrow_12(o: Any=None, d: dep=d) -> Component:
        return obj_to_comp(dep_reflection(), o)
    
    return show_doc(default_render_options, serialize_comp(arrow_12(d)))


