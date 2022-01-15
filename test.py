from _fable_pykg.program import *
from _fable_pykg_infr.fetch_dependencies import get_deps, DEFAULT_MIRROR
from pprint import pprint
pprint(get_deps(DEFAULT_MIRROR, "fspy/fable-pykg"))

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

# from _fable_pykg_infr.async_request_github import get_async_result, request_github_package_versions, request_github_package_with_tag
# from _fable_pykg_infr.init import parse
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

# from _fable_pykg_infr.async_request_pypi import (
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
