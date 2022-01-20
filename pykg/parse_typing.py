from __future__ import annotations
import ast
from tkinter.tix import IMMEDIATE
import typing
import sys
from collections import ChainMap
from pykg.component import TypeInfo

HAS_SPECIAL_SLICE = False
PY39 = True
TypeInstFuncName = "__Pykg_GenSpec"
TypeToReflectFuncName = "__Pykg_TypeReflect"
ReflectOrFuncName = "__Pykg_ReflectOr"

if sys.version_info < (3, 9):
    HAS_SPECIAL_SLICE = True
    PY39 = False


def mod_to_expr(mod: ast.Module):
    assert isinstance(mod, ast.Module)
    fst = mod.body[0]
    assert isinstance(fst, ast.Expr)
    return fst.value


class TypeEval(ast.NodeTransformer):
    def __init__(self, scope: dict[str, str]):
        self.scope = scope

    # XXX: support 'Literal[x] where x : str' ?
    def visit_Constant(self, node: ast.Constant):
        if isinstance(node.value, str):
            return self.visit_Str(node) # type: ignore
        return node

    def visit_Str(self, node: ast.Str):
        mod = ast.parse(node.value)
        expr = mod_to_expr(mod)
        return self.visit(expr)

    def visit_Attribute(self, node: ast.Attribute):
        reflect_func = ast.Name(id=TypeToReflectFuncName, ctx=ast.Load())
        return ast.Call(
            func=reflect_func,
            args=[node],
            keywords=[],
        )

    def visit_BinOp(self, node: ast.BinOp):
        if isinstance(node.op, ast.BitOr):
            or_func = ast.Name(id=ReflectOrFuncName, ctx=ast.Load())
            return ast.Call(
                func=or_func,
                args=[self.visit(node.left), self.visit(node.right)],
                keywords=[],
            )
        raise TypeError(f"a type expression does not allow binary operator {node.op.__class__.__name__}.")


    def visit_Name(self, node: ast.Name):
        if nid := self.scope.get(node.id):
            assert isinstance(nid, str)
            setattr(node, "id", nid)

        reflect_func = ast.Name(id=TypeToReflectFuncName, ctx=ast.Load())

        return ast.Call(
            func=reflect_func,
            args=[node],
            keywords=[],
        )

    def visit_Subscript(self, node: ast.Subscript):
        generic_type = node.value
        if HAS_SPECIAL_SLICE:
            if isinstance(node.slice, (ast.Slice, ast.ExtSlice)):
                raise TypeError("slices in Type subscript.")
            assert isinstance(node.slice, ast.Index)
            index = node.slice.value
        else:
            if isinstance(node.slice, ast.Slice):
                raise TypeError("slices in Type subscript.")
            index = typing.cast(ast.expr, node.slice)
        if isinstance(index, ast.Tuple):
            arguments = index.elts
        else:
            arguments = [index]
        arguments = typing.cast(
            typing.List[ast.expr], list(map(self.visit, arguments)))
        # https://raw.githubusercontent.com/python/cpython/3.x/Parser/Python.asdl
        inst_func = ast.Name(id=TypeInstFuncName, ctx=ast.Load())

        return ast.Call(
            func=inst_func,
            args=[generic_type, *arguments],
            keywords=[],
        )


def parse_typing(s: str, scope: typing.Dict[str, object], specializer, type_reflect, reflect_or) -> TypeInfo:
    expr = mod_to_expr(ast.parse(s))
    # bidirectional map
    expr_ = TypeEval({}).visit(expr)
    ast.fix_missing_locations(expr_)
    expr_ = ast.Expression(body=expr_)
    local_scope = {
        TypeInstFuncName: specializer,
        TypeToReflectFuncName: type_reflect,
        ReflectOrFuncName: reflect_or,
    }

    co = compile(expr_, "<pykg_type_eval>", "eval")
    expr = eval(co, scope, local_scope)
    return expr


if __name__ == '__main__':
    print(
        parse_typing(
            "list[int]",
            {},
            specializer=lambda f, *args: f"{f}<{', '.join(args)}>",
            type_reflect=lambda t: t.__name__,
            reflect_or=None
        )
    )
