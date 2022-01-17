from __future__ import annotations
from .comfig_require import (one_or_list,sink_comments,mk_specifier_set,mk_specifier,parse_version,CCommented,CList,CCons,CSpec,CVer,CBool,CStr,CNum,CNull,Component,COMPACT,PATCH,LE,GE,LT,GT,NE,EQ,operator,toArray,add,toNum,lexeme,unesc,SpecifierSet,specifier,version,array,num)
from .comfig_lexer import lexall as lexall
from .comfig_construct import *
from lark.lexer import Lexer as Lexer
from lark import Transformer as Transformer
from lark import Lark as Lark
from _tbnf.FableSedlex.sedlex import from_ustring as from_ustring
tokenmaps = ["_I__H__J__I_", "_I__M__M__I_", "_I__I__I_", "_I__I__J__I_", "_I__J__J__I_", "_I__K__I_", "_I__K__J__I_", "_I__Q__I_", "_I_FALSE_I_", "_I_FORMAT_I_", "_I_NULL_I_", "_I_TRUE_I_", "_I__T__I_", "_I__V__I_", "_I__W__I_", "EXP", "ID", "LINE_COMMENT", "STR", "VERSION", "UNKNOWN"]
tokenreprs = ["\"!=\"", "\"&&\"", "\"<\"", "\"<=\"", "\"==\"", "\">\"", "\">=\"", "\"^\"", "\"false\"", "\"format\"", "\"null\"", "\"true\"", "\"{\"", "\"}\"", "\"~\"", "EXP", "ID", "LINE_COMMENT", "STR", "VERSION", "UNKNOWN"]

def construct_token(token_id, lexeme, line, col, span, offset, file):
    if token_id == -1: return token("EOF", "")
    return token(tokenmaps[token_id], lexeme, offset, line, col, None, None, span + offset)

def is_eof(token):
    return token.type == "EOF"
class Sedlex(Lexer):
    def __init__(self, lex_conf):
        pass
    def lex(self, raw_string):
        lexbuf = from_ustring(raw_string)
        return lexall(lexbuf, construct_token, is_eof)

class RBNFTransformer(Transformer):
    def component_1(self, __tbnf_COMPONENTS):
        return CCommented(__tbnf_COMPONENTS[0], __tbnf_COMPONENTS[1])
    
    def component_0(self, __tbnf_COMPONENTS):
        return __tbnf_COMPONENTS[0]
    
    def list_o_comment_p__1(self, __tbnf_COMPONENTS):
        return add(__tbnf_COMPONENTS[0], __tbnf_COMPONENTS[1])
    
    def list_o_comment_p__0(self, __tbnf_COMPONENTS):
        return [__tbnf_COMPONENTS[0]]
    
    def comp_9(self, __tbnf_COMPONENTS):
        return CList([])
    
    def comp_8(self, __tbnf_COMPONENTS):
        return CList(__tbnf_COMPONENTS[1])
    
    def comp_7(self, __tbnf_COMPONENTS):
        return CCons(lexeme(__tbnf_COMPONENTS[0]), __tbnf_COMPONENTS[1])
    
    def comp_6(self, __tbnf_COMPONENTS):
        return CSpec(mk_specifier_set(__tbnf_COMPONENTS[0]))
    
    def comp_5(self, __tbnf_COMPONENTS):
        return CVer(__tbnf_COMPONENTS[0])
    
    def comp_4(self, __tbnf_COMPONENTS):
        return CNull()
    
    def comp_3(self, __tbnf_COMPONENTS):
        return CBool(False)
    
    def comp_2(self, __tbnf_COMPONENTS):
        return CBool(True)
    
    def comp_1(self, __tbnf_COMPONENTS):
        return CStr(unesc(lexeme(__tbnf_COMPONENTS[0])))
    
    def comp_0(self, __tbnf_COMPONENTS):
        return CNum(toNum(lexeme(__tbnf_COMPONENTS[0])))
    
    def list_o_component_p__1(self, __tbnf_COMPONENTS):
        return add(__tbnf_COMPONENTS[0], __tbnf_COMPONENTS[1])
    
    def list_o_component_p__0(self, __tbnf_COMPONENTS):
        return [__tbnf_COMPONENTS[0]]
    
    def id_1(self, __tbnf_COMPONENTS):
        return __tbnf_COMPONENTS[0]
    
    def id_0(self, __tbnf_COMPONENTS):
        return __tbnf_COMPONENTS[0]
    
    def comment_0(self, __tbnf_COMPONENTS):
        return lexeme(__tbnf_COMPONENTS[0])
    
    def specifier_set_1(self, __tbnf_COMPONENTS):
        return add(__tbnf_COMPONENTS[0], __tbnf_COMPONENTS[2])
    
    def specifier_set_0(self, __tbnf_COMPONENTS):
        return [__tbnf_COMPONENTS[0]]
    
    def specifier_0(self, __tbnf_COMPONENTS):
        return mk_specifier(__tbnf_COMPONENTS[0], __tbnf_COMPONENTS[1])
    
    def version_0(self, __tbnf_COMPONENTS):
        return parse_version(lexeme(__tbnf_COMPONENTS[0]))
    
    def op_7(self, __tbnf_COMPONENTS):
        return COMPACT
    
    def op_6(self, __tbnf_COMPONENTS):
        return PATCH
    
    def op_5(self, __tbnf_COMPONENTS):
        return LE
    
    def op_4(self, __tbnf_COMPONENTS):
        return GE
    
    def op_3(self, __tbnf_COMPONENTS):
        return LT
    
    def op_2(self, __tbnf_COMPONENTS):
        return GT
    
    def op_1(self, __tbnf_COMPONENTS):
        return NE
    
    def op_0(self, __tbnf_COMPONENTS):
        return EQ
    
    def start_0(self, __tbnf_COMPONENTS):
        return (__tbnf_COMPONENTS[1], __tbnf_COMPONENTS[2])
    
    pass

with (__import__('pathlib').Path(__file__).parent /'comfig.lark').open(encoding='utf8') as __0123fx9:
    grammar = __0123fx9.read()

parser = Lark(grammar, start='start', parser='lalr', lexer=Sedlex, transformer=RBNFTransformer(), keep_all_tokens=True)
