from __future__ import annotations
# from _fable_pykg.program import *
# from _fable_pykg.src.proj import parse_metadata
# from reflect.fetch_dependencies import get_deps_from_metadata, DEFAULT_MIRROR, DependencyUnsatisfied
# from reflect.log import error
# from pprint import pprint

# metadata = parse_metadata(open("../comf-index/fspy/F/fable-pykg.comf").read())
# try:
#     pprint(get_deps_from_metadata("file:///../comf-index", metadata, {'pypi/lark': '.hidden/lark.comf'}))
# except DependencyUnsatisfied as e:
#     error('dependencies not sastified:\n' + '\n'.join(['- ' + line for line in e.unsatisified_reasons]))

from dataclasses import dataclass
import typing
from pprint import pprint
from pykg.data_reflection import reflect, reflect_opt, type_reflection, get_reflection_opts, from_comf, to_comf
from pykg.component import CNum, CStr, Commented
from pykg.project import Project, Metadata
from pykg.fetch_dependencies import get_deps_from_metadata, DEFAULT_MIRROR
from pykg.fspy_builder import FsPyBuilder

p_tinfo = type_reflection(Project)
m_tinfo = type_reflection(Metadata)

print(to_comf(from_comf(Project, r"""
format v0.1
project
{
    "a/b" v0.2
    mirror "sda"
    src {
        "sda"
        "asda"
    }

    local { "pypi/lark" url {"sdadsa" git-branch "main" } }
}
""")))



meta = from_comf(Metadata, r"""
format v0.1
metadata
{
    "a/b"
    dist {   
        v0.1
        dep { "pypi/lark" >= v0.1 }
    }
}
""")


req = get_deps_from_metadata(DEFAULT_MIRROR, meta, {})
lock_project = FsPyBuilder(req).lock()
ss = to_comf(lock_project)


# @reflect
# @reflect_opt('name', recogniser=lambda x: isinstance(x, CStr))
# @dataclass
# class Author:
#     name: str
#     email: typing.Optional[str] = ""


# @reflect
# @reflect_opt('x', recogniser=lambda x: isinstance(x, CNum))
# @reflect_opt("xs", lift_to_array=True)
# @dataclass
# class S_K:
#     x: int | None
#     xs: list[Commented[Author]]

# tinfo = type_reflection(S_K)

# # data = tinfo.deconstruct(S(1, [Com Author("asda"), Author('uuu')]))
# # pprint(data)

# print(get_reflection_opts(Author))

# from reflect.init import parse

# res = parse(r"""
# format v0.1
# s-k {
#     1
#     -- asda
#     author "a"
#     -- asdas
#     author "b"
# }
# """)

# pprint(res)
# pprint(tinfo.construct(res))





# test_load_meta(r"""
# format v0.1
# metadata
# {
#     "lang/const"
#     author "taine"
#     dist
#     {
#         v0.1
#         dep { "lang/python" >= v3.8 }
#         dep { "fspy/fable-sedlex" >= v2.8 }
#     }
# }
# """)


# test_load_proj(r"""
# format v0.1
# project
# {
#     "lang/const" v0.1
#     author "taine"
#     mirror "default"
#     builder "default"
#     dep { "lang/python" >= v3.8 }
#     dep { "fspy/fable-sedlex" >= v2.8 }
#     src [
#         "a.fs"
#         "b.fs"
#     ]
# }
# """)

# test_load_meta(r"""
# format v0.1
# metadata
# {
#     "lang/python"
#     dist v3.8.8
# }
# """)

# from reflect.async_request_github import get_async_result, request_github_package_versions, request_github_package_with_tag
# from reflect.init import parse
# print(parse(r"""
# v0.1.0
# project{
#     "fable.sedlex"
#     author "thautwarm"
#     version v0.2
#     deps [ ]
#     src [
#        "Sedlex.fs"
#        "CodeGen.fs"
#        "CodeGen.Python.fs"
#     ]
# }
# """))

# print(request_github_package_versions("thautwarm/fable.sedlex"))

# print(get_async_result(request_github_package_with_tag("thautwarm/fable.sedlex", "v0.1")))

# from reflect.async_request_pypi import (
#     require_python_package_versions_and_deps,
#     get_async_result,
# )

# print(
#     list(
#         filter(
#             None,
#             get_async_result(
#                 require_python_package_versions_and_deps("scikit-learn", False)
#             ),
#         )
#     )
# )
# x = parser.parse(
# r"""
# f {
#     1
#     2
#     3
#     dep {
#         "asda"
#         name "as"
#         >= v1.2
#         <= v1.2
#         rc [1 2 3 4]
#     }
#     "asda"
# }


# """)
# print(x)

# from _fable_pykg.src.z3 import test

# test()


# print(main(r"""
# project{
#     author "a"
#     version v0.1
#     -- asxd
#     deps [
#     ]
# }
# """))
# if False:
#     main(r"""


#     project{
#         author "thautwarm"
#         version v0.1
#         -- some comments
#         deps [
#             GitHub { repo "thautwarm/fable-sedlex" version [^v0.2] }
#             PyPI { name "lark" version [v1.0] }
#         ]
#     }
#     """)
