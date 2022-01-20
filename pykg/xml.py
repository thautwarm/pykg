from __future__ import annotations
from dataclasses import dataclass
from . import pretty_doc as doc
from xml.sax.saxutils import escape
import json

slash = doc.seg("/")

@dataclass
class XML:
    name: str
    attributes: list[tuple[str, object]]
    contents: list[XML] | str = ""
    paired: bool = True

    def to_doc(self):
        return to_doc(self)

def _dump_o(o: object):
    if isinstance(o, int):
        return doc.pretty(o)
    return doc.seg(escape(json.dumps(str(o))))

def to_doc(self: XML) -> doc.Doc:
    if self.attributes:
        attrs = doc.space * doc.seplistof(doc.space, (doc.seg(attr) * doc.seg('=') * _dump_o(v) for attr, v in self.attributes))
    else:
        attrs = doc.empty
    if self.paired:
        if isinstance(self.contents, list):
            return doc.vsep([
                doc.angle(doc.seg(self.name) * attrs),
                doc.indent(4, doc.vsep(list(map(to_doc, self.contents)))),
                doc.angle(slash * doc.seg(self.name))
            ])
        return doc.angle(doc.seg(self.name) * attrs) * doc.indent(4, doc.seg(escape(self.contents))) * doc.angle(slash * doc.seg(self.name))
    assert not self.contents
    return doc.angle(doc.seg(self.name) * attrs * slash)


def xml(name: str, content: list[XML] | str | None, **attrs) -> XML:
    if content is None:
        return XML(name, list(attrs.items()), "", False)
    return XML(name, list(attrs.items()), content, True)