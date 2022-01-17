from _tbnf.FableSedlex.sedlex import *
import typing
import typing_extensions
import dataclasses
_sedlex_rnd_157 = [ 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, None, 18, 19, 20, -1 ]  # token_ids

def _sedlex_st_57(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 20)
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_156[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_155(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_57(lexerbuf)
    return result

def _sedlex_st_56(lexerbuf: lexbuf):
    result = -1
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_154[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_153(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_57(lexerbuf)
    return result

def _sedlex_st_55(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 20)
    state_id = _sedlex_decide_23(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_152[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_23(c: int):
    if c <= 45:
        return -1
    else:
        if c <= 57:
            return _sedlex_DT_table_20[c - 46] - 1
        else:
            return -1

def _sedlex_rnd_151(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_55(lexerbuf)
    return result

def _sedlex_rnd_150(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_56(lexerbuf)
    return result

def _sedlex_st_54(lexerbuf: lexbuf):
    result = -1
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_149[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_148(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_55(lexerbuf)
    return result

def _sedlex_st_53(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_22(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_147[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_22(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_19[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_146(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_53(lexerbuf)
    return result

def _sedlex_rnd_145(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_54(lexerbuf)
    return result

def _sedlex_rnd_144(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_52(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_12(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_143[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_142(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_53(lexerbuf)
    return result

def _sedlex_rnd_141(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_51(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 11)
    state_id = _sedlex_decide_11(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_140[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_139(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_50(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_16(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_138[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_137(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_51(lexerbuf)
    return result

def _sedlex_rnd_136(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_49(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_21(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_135[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_134(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_50(lexerbuf)
    return result

def _sedlex_rnd_133(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_48(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_17(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_132[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_131(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_49(lexerbuf)
    return result

def _sedlex_rnd_130(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_47(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 10)
    state_id = _sedlex_decide_11(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_129[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_128(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_46(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_14(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_127[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_126(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_47(lexerbuf)
    return result

def _sedlex_rnd_125(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_45(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_14(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_124[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_123(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_46(lexerbuf)
    return result

def _sedlex_rnd_122(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_44(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_21(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_121[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_21(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_18[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_120(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_45(lexerbuf)
    return result

def _sedlex_rnd_119(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_43(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 9)
    state_id = _sedlex_decide_11(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_118[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_117(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_42(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_20(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_116[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_20(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_17[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_115(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_43(lexerbuf)
    return result

def _sedlex_rnd_114(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_41(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_19(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_113[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_19(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_16[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_112(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_42(lexerbuf)
    return result

def _sedlex_rnd_111(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_40(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_18(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_110[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_18(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_15[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_109(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_41(lexerbuf)
    return result

def _sedlex_rnd_108(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_39(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_17(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_107[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_17(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_14[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_106(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_40(lexerbuf)
    return result

def _sedlex_rnd_105(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_38(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 8)
    state_id = _sedlex_decide_11(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_104[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_103(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_37(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_16(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_102[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_16(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_13[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_101(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_38(lexerbuf)
    return result

def _sedlex_rnd_100(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_36(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_15(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_99[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_15(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_12[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_98(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_37(lexerbuf)
    return result

def _sedlex_rnd_97(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_35(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_14(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_96[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_14(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_11[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_95(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_36(lexerbuf)
    return result

def _sedlex_rnd_94(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_34(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_13(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_93[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_13(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_10[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_92(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_39(lexerbuf)
    return result

def _sedlex_rnd_91(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_35(lexerbuf)
    return result

def _sedlex_rnd_90(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_32(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_12(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_89[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_88(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_32(lexerbuf)
    return result

def _sedlex_rnd_87(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_31(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_12(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_86[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_12(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_9[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_85(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_32(lexerbuf)
    return result

def _sedlex_rnd_84(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_30(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_11(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_83[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_82(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_29(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 16)
    state_id = _sedlex_decide_11(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_81[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_11(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 122:
            return _sedlex_DT_table_8[c - 45] - 1
        else:
            if c <= 19967:
                return -1
            else:
                if c <= 40869:
                    return 0
                else:
                    return -1

def _sedlex_rnd_80(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_30(lexerbuf)
    return result

def _sedlex_st_27(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 5)
    state_id = _sedlex_decide_3(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_79[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_78(lexerbuf: lexbuf):
    result = -1
    result = 6
    return result

def _sedlex_st_25(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 21)
    state_id = _sedlex_decide_3(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_77[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_76(lexerbuf: lexbuf):
    result = -1
    result = 4
    return result

def _sedlex_st_23(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 2)
    state_id = _sedlex_decide_3(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_75[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_74(lexerbuf: lexbuf):
    result = -1
    result = 3
    return result

def _sedlex_st_22(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_10(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_73[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_72(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_18(lexerbuf)
    return result

def _sedlex_rnd_71(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_20(lexerbuf)
    return result

def _sedlex_rnd_70(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_16(lexerbuf)
    return result

def _sedlex_st_21(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 21)
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_69[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_68(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_17(lexerbuf)
    return result

def _sedlex_st_20(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_10(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_67[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_10(c: int):
    if c <= 45:
        return -1
    else:
        if c <= 101:
            return _sedlex_DT_table_7[c - 46] - 1
        else:
            return -1

def _sedlex_rnd_66(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_18(lexerbuf)
    return result

def _sedlex_rnd_65(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_20(lexerbuf)
    return result

def _sedlex_rnd_64(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_16(lexerbuf)
    return result

def _sedlex_st_19(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_63[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_62(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_19(lexerbuf)
    return result

def _sedlex_st_18(lexerbuf: lexbuf):
    result = -1
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_61[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_60(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_19(lexerbuf)
    return result

def _sedlex_st_17(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_9(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_59[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_9(c: int):
    if c <= 47:
        return -1
    else:
        if c <= 101:
            return _sedlex_DT_table_6[c - 48] - 1
        else:
            return -1

def _sedlex_rnd_58(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_18(lexerbuf)
    return result

def _sedlex_rnd_57(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_17(lexerbuf)
    return result

def _sedlex_st_16(lexerbuf: lexbuf):
    result = -1
    state_id = _sedlex_decide_8(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_56[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_8(c: int):
    if c <= 47:
        return -1
    else:
        if c <= 57:
            return 0
        else:
            return -1

def _sedlex_rnd_55(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_17(lexerbuf)
    return result

def _sedlex_st_15(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 17)
    state_id = _sedlex_decide_7(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_54[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_7(c: int):
    if c <= -1:
        return -1
    else:
        if c <= 12:
            return _sedlex_DT_table_5[c - 0] - 1
        else:
            if c <= 13:
                return -1
            else:
                return 0

def _sedlex_rnd_53(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_15(lexerbuf)
    return result

def _sedlex_st_14(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_6(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_52[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_6(c: int):
    if c <= 44:
        return -1
    else:
        if c <= 101:
            return _sedlex_DT_table_4[c - 45] - 1
        else:
            return -1

def _sedlex_rnd_51(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_18(lexerbuf)
    return result

def _sedlex_rnd_50(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_20(lexerbuf)
    return result

def _sedlex_rnd_49(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_16(lexerbuf)
    return result

def _sedlex_rnd_48(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_15(lexerbuf)
    return result

def _sedlex_st_12(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 21)
    state_id = _sedlex_decide_5(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_47[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_5(c: int):
    if c <= 37:
        return -1
    else:
        if c <= 38:
            return 0
        else:
            return -1

def _sedlex_rnd_46(lexerbuf: lexbuf):
    result = -1
    result = 1
    return result

def _sedlex_st_11(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 19)
    state_id = _sedlex_decide_4(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_45[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_44(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_10(lexerbuf)
    return result

def _sedlex_rnd_43(lexerbuf: lexbuf):
    result = -1
    result = 19
    return result

def _sedlex_rnd_42(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_8(lexerbuf)
    return result

def _sedlex_st_10(lexerbuf: lexbuf):
    result = -1
    state_id = _sedlex_decide_4(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_41[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_40(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_10(lexerbuf)
    return result

def _sedlex_rnd_39(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_11(lexerbuf)
    return result

def _sedlex_rnd_38(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_8(lexerbuf)
    return result

def _sedlex_st_8(lexerbuf: lexbuf):
    result = -1
    state_id = _sedlex_decide_4(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_37[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_36(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_10(lexerbuf)
    return result

def _sedlex_rnd_35(lexerbuf: lexbuf):
    result = -1
    result = 19
    return result

def _sedlex_rnd_34(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_8(lexerbuf)
    return result

def _sedlex_st_7(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 21)
    state_id = _sedlex_decide_4(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_33[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_4(c: int):
    if c <= -1:
        return -1
    else:
        if c <= 92:
            return _sedlex_DT_table_3[c - 0] - 1
        else:
            return 0

def _sedlex_rnd_32(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_10(lexerbuf)
    return result

def _sedlex_rnd_31(lexerbuf: lexbuf):
    result = -1
    result = 19
    return result

def _sedlex_rnd_30(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_8(lexerbuf)
    return result

def _sedlex_st_5(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 21)
    state_id = _sedlex_decide_3(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_29[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_3(c: int):
    if c <= 60:
        return -1
    else:
        if c <= 61:
            return 0
        else:
            return -1

def _sedlex_rnd_28(lexerbuf: lexbuf):
    result = -1
    result = 0
    return result

def _sedlex_st_4(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 18)
    state_id = _sedlex_decide_2(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_27[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_rnd_26(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_4(lexerbuf)
    return result

def _sedlex_st_3(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 18)
    state_id = _sedlex_decide_2(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_25[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_2(c: int):
    if c <= 8:
        return -1
    else:
        if c <= 32:
            return _sedlex_DT_table_2[c - 9] - 1
        else:
            return -1

def _sedlex_rnd_24(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_4(lexerbuf)
    return result

def _sedlex_st_0(lexerbuf: lexbuf):
    result = -1
    mark(lexerbuf, 15)
    state_id = _sedlex_decide_1(public_next_int(lexerbuf))
    if state_id >= 0:
        result = _sedlex_rnd_23[state_id](lexerbuf)
    else:
        result = backtrack(lexerbuf)
    return result

def _sedlex_decide_1(c: int):
    if c <= 126:
        return _sedlex_DT_table_1[c - -1] - 1
    else:
        if c <= 40869:
            if c <= 19967:
                return 1
            else:
                return 12
        else:
            return 1

def _sedlex_rnd_22(lexerbuf: lexbuf):
    result = -1
    result = 14
    return result

def _sedlex_rnd_21(lexerbuf: lexbuf):
    result = -1
    result = 13
    return result

def _sedlex_rnd_20(lexerbuf: lexbuf):
    result = -1
    result = 12
    return result

def _sedlex_rnd_19(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_52(lexerbuf)
    return result

def _sedlex_rnd_18(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_48(lexerbuf)
    return result

def _sedlex_rnd_17(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_44(lexerbuf)
    return result

def _sedlex_rnd_16(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_34(lexerbuf)
    return result

def _sedlex_rnd_15(lexerbuf: lexbuf):
    result = -1
    result = 7
    return result

def _sedlex_rnd_14(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_31(lexerbuf)
    return result

def _sedlex_rnd_13(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_29(lexerbuf)
    return result

def _sedlex_rnd_12(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_27(lexerbuf)
    return result

def _sedlex_rnd_11(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_25(lexerbuf)
    return result

def _sedlex_rnd_10(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_23(lexerbuf)
    return result

def _sedlex_rnd_9(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_22(lexerbuf)
    return result

def _sedlex_rnd_8(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_21(lexerbuf)
    return result

def _sedlex_rnd_7(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_14(lexerbuf)
    return result

def _sedlex_rnd_6(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_12(lexerbuf)
    return result

def _sedlex_rnd_5(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_7(lexerbuf)
    return result

def _sedlex_rnd_4(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_5(lexerbuf)
    return result

def _sedlex_rnd_3(lexerbuf: lexbuf):
    result = -1
    result = _sedlex_st_3(lexerbuf)
    return result

def _sedlex_rnd_2(lexerbuf: lexbuf):
    result = -1
    result = 21
    return result

def _sedlex_rnd_1(lexerbuf: lexbuf):
    result = -1
    result = 22
    return result


@dataclasses.dataclass
class Token:
    token_id: int
    lexeme : str
    line: int
    col: int
    span: int
    offset: int
    file: str

_Token = typing.TypeVar("_Token")

class TokenConstructor(typing_extensions.Protocol[_Token]):
    def __call__(self, token_id: int, lexeme: str, line: int, col: int, span: int, offset: int, file: str) -> _Token: ...

def lex(lexerbuf: lexbuf ,  construct_token: TokenConstructor[_Token]=Token):
    start(lexerbuf)
    case_id = _sedlex_st_0(lexerbuf)
    if case_id < 0: raise Exception("the last branch must be a catch-all error case!")
    token_id = _sedlex_rnd_157[case_id]
    if token_id is not None:
        return construct_token(token_id, lexeme(lexerbuf), lexerbuf.start_line, lexerbuf.pos - lexerbuf.curr_bol, lexerbuf.pos - lexerbuf.start_pos, lexerbuf.start_pos, lexerbuf.filename)
    return None
def lexall(buf: lexbuf, construct: TokenConstructor[_Token], is_eof: Callable[[_Token], bool]):
    while True:
        token = lex(buf, construct)
        if token is None: continue
        if is_eof(token): break
        yield token
_sedlex_rnd_156 = [_sedlex_rnd_155]

_sedlex_rnd_154 = [_sedlex_rnd_153]

_sedlex_DT_table_20 = [1, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]

_sedlex_rnd_152 = [_sedlex_rnd_150, _sedlex_rnd_151]

_sedlex_rnd_149 = [_sedlex_rnd_148]

_sedlex_DT_table_19 = [1, 2, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_147 = [_sedlex_rnd_144, _sedlex_rnd_145, _sedlex_rnd_146]

_sedlex_rnd_143 = [_sedlex_rnd_141, _sedlex_rnd_142]

_sedlex_rnd_140 = [_sedlex_rnd_139]

_sedlex_rnd_138 = [_sedlex_rnd_136, _sedlex_rnd_137]

_sedlex_rnd_135 = [_sedlex_rnd_133, _sedlex_rnd_134]

_sedlex_rnd_132 = [_sedlex_rnd_130, _sedlex_rnd_131]

_sedlex_rnd_129 = [_sedlex_rnd_128]

_sedlex_rnd_127 = [_sedlex_rnd_125, _sedlex_rnd_126]

_sedlex_rnd_124 = [_sedlex_rnd_122, _sedlex_rnd_123]

_sedlex_DT_table_18 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1]

_sedlex_rnd_121 = [_sedlex_rnd_119, _sedlex_rnd_120]

_sedlex_rnd_118 = [_sedlex_rnd_117]

_sedlex_DT_table_17 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_116 = [_sedlex_rnd_114, _sedlex_rnd_115]

_sedlex_DT_table_16 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_113 = [_sedlex_rnd_111, _sedlex_rnd_112]

_sedlex_DT_table_15 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_110 = [_sedlex_rnd_108, _sedlex_rnd_109]

_sedlex_DT_table_14 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_107 = [_sedlex_rnd_105, _sedlex_rnd_106]

_sedlex_rnd_104 = [_sedlex_rnd_103]

_sedlex_DT_table_13 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_102 = [_sedlex_rnd_100, _sedlex_rnd_101]

_sedlex_DT_table_12 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_99 = [_sedlex_rnd_97, _sedlex_rnd_98]

_sedlex_DT_table_11 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_96 = [_sedlex_rnd_94, _sedlex_rnd_95]

_sedlex_DT_table_10 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_93 = [_sedlex_rnd_90, _sedlex_rnd_91, _sedlex_rnd_92]

_sedlex_rnd_89 = [_sedlex_rnd_87, _sedlex_rnd_88]

_sedlex_DT_table_9 = [1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_86 = [_sedlex_rnd_84, _sedlex_rnd_85]

_sedlex_rnd_83 = [_sedlex_rnd_82]

_sedlex_DT_table_8 = [1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

_sedlex_rnd_81 = [_sedlex_rnd_80]

_sedlex_rnd_79 = [_sedlex_rnd_78]

_sedlex_rnd_77 = [_sedlex_rnd_76]

_sedlex_rnd_75 = [_sedlex_rnd_74]

_sedlex_rnd_73 = [_sedlex_rnd_70, _sedlex_rnd_71, _sedlex_rnd_72]

_sedlex_rnd_69 = [_sedlex_rnd_68]

_sedlex_DT_table_7 = [1, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3]

_sedlex_rnd_67 = [_sedlex_rnd_64, _sedlex_rnd_65, _sedlex_rnd_66]

_sedlex_rnd_63 = [_sedlex_rnd_62]

_sedlex_rnd_61 = [_sedlex_rnd_60]

_sedlex_DT_table_6 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2]

_sedlex_rnd_59 = [_sedlex_rnd_57, _sedlex_rnd_58]

_sedlex_rnd_56 = [_sedlex_rnd_55]

_sedlex_DT_table_5 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1]

_sedlex_rnd_54 = [_sedlex_rnd_53]

_sedlex_DT_table_4 = [1, 2, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4]

_sedlex_rnd_52 = [_sedlex_rnd_48, _sedlex_rnd_49, _sedlex_rnd_50, _sedlex_rnd_51]

_sedlex_rnd_47 = [_sedlex_rnd_46]

_sedlex_rnd_45 = [_sedlex_rnd_42, _sedlex_rnd_43, _sedlex_rnd_44]

_sedlex_rnd_41 = [_sedlex_rnd_38, _sedlex_rnd_39, _sedlex_rnd_40]

_sedlex_rnd_37 = [_sedlex_rnd_34, _sedlex_rnd_35, _sedlex_rnd_36]

_sedlex_DT_table_3 = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]

_sedlex_rnd_33 = [_sedlex_rnd_30, _sedlex_rnd_31, _sedlex_rnd_32]

_sedlex_rnd_29 = [_sedlex_rnd_28]

_sedlex_rnd_27 = [_sedlex_rnd_26]

_sedlex_DT_table_2 = [1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

_sedlex_rnd_25 = [_sedlex_rnd_24]

_sedlex_DT_table_1 = [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 4, 5, 2, 2, 2, 6, 2, 2, 2, 2, 2, 2, 7, 8, 2, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 2, 2, 10, 11, 12, 2, 2, 13, 13, 13, 13, 14, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 2, 2, 2, 15, 13, 2, 13, 13, 13, 13, 14, 16, 13, 13, 13, 13, 13, 13, 13, 17, 13, 13, 13, 13, 13, 18, 13, 19, 13, 13, 13, 13, 20, 2, 21, 22]

_sedlex_rnd_23 = [_sedlex_rnd_1, _sedlex_rnd_2, _sedlex_rnd_3, _sedlex_rnd_4, _sedlex_rnd_5, _sedlex_rnd_6, _sedlex_rnd_7, _sedlex_rnd_8, _sedlex_rnd_9, _sedlex_rnd_10, _sedlex_rnd_11, _sedlex_rnd_12, _sedlex_rnd_13, _sedlex_rnd_14, _sedlex_rnd_15, _sedlex_rnd_16, _sedlex_rnd_17, _sedlex_rnd_18, _sedlex_rnd_19, _sedlex_rnd_20, _sedlex_rnd_21, _sedlex_rnd_22]

