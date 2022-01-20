import typing
from .comfig_parser import parser, tokenreprs, tokenmaps
from lark import UnexpectedToken, Token
from .errors import InvalidComfigVersion
from .version import Version

_restore_literals = dict(zip(tokenmaps, tokenreprs))
if typing.TYPE_CHECKING:
    from .component import Component


def parse(s: str):
    try:
        ver, comp = typing.cast('tuple[Version, Component]', parser.parse(s))
        e_set = None
        if ver.major == 0 and ver.minor == 1:
            pass
        else:
            raise InvalidComfigVersion(f"expect version v0.1.*, got {ver}")
        return comp
    except UnexpectedToken as e:
        expected = set([_restore_literals[each] for each in e.expected])
        tk: Token = getattr(e, "token")
        tk = Token.new_borrow_pos(_restore_literals[tk.type], tk.value, tk)
        e_set = UnexpectedToken(tk, expected)

    raise e_set


__all__ = ["parse"]
