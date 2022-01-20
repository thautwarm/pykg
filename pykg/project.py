from __future__ import annotations
from .component import *
from dataclasses import dataclass
from .data_reflection import reflect_opt, reflect, erase_typename
from .classified_url import classify_url, ClassifiedUrl


@reflect_opt(fieldname="link", recogniser=lambda x: isinstance(x, CStr))
@erase_typename
@reflect
@dataclass
class Url:
    link: Commented[str]
    # if set, is a git repo
    git_branch: Commented[str] | None = None

    @classmethod
    def raw_url(cls, url: str):
        return Url(Commented([], url), None)


@reflect
@reflect_opt(fieldname="name", recogniser=lambda x: isinstance(x, CStr))
@dataclass
class Author:
    name: Commented[str]
    email: str | None


@reflect
@reflect_opt("authors", lift_to_array=True)
@reflect_opt("locals", lift_to_array=True)
@reflect_opt("deps", lift_to_array=True)
@reflect_opt("src", default=[])
@reflect_opt("name", recogniser=lambda x: isinstance(x, CStr))
@reflect_opt("version", recogniser=lambda x: isinstance(x, CVer))
@dataclass
class Project:
    name: Commented[str]
    mirror: Commented[str] | None
    version: Commented[Version]
    authors: list[Commented[Author]]
    builder: Commented[str] | None
    locals: list[Commented[Local]]
    src: Commented[list[Commented[str]]]
    deps: list[Commented[Dep]]
    exe: Commented[str] | None


@reflect
@reflect_opt(fieldname="package", recogniser=lambda x: isinstance(x, CStr))
@dataclass
class Local:
    package: Commented[str]
    # A url to local path of metadata (xxx.comf) or the project file ('project.comf');
    # if `project.toml` is linked, a metadata with only 1 dist is automatically generated
    # when solving pakcages.
    url: Commented[Url]


@reflect
@reflect_opt(fieldname="name", recogniser=lambda x: isinstance(x, CStr))
@reflect_opt(fieldname="version", recogniser=lambda x: isinstance(x, CSpec))
@dataclass
class Dep:
    name: Commented[str]
    version: Commented[SpecifierSet]

    @classmethod
    def mk(cls, name: str, version: SpecifierSet):
        return cls(cmt(name), cmt(version))


@reflect
@reflect_opt("name", recogniser=lambda x: isinstance(x, CStr))
@reflect_opt("authors", lift_to_array=True)
@reflect_opt("distributions", lift_to_array=True)
@dataclass
class Metadata:
    name: Commented[str]
    authors: list[Commented[Author]]
    distributions: list[Commented[Dist]]


@reflect
@reflect_opt("version", recogniser=lambda x: isinstance(x, CVer))
@reflect_opt("deps", lift_to_array=True)
@dataclass
class Dist:
    version: Commented[Version]
    # url of project
    url: Commented[Url] | None
    deps: list[Commented[Dep]]


PackageId = str


def create_metadata_from_project(url_o: ClassifiedUrl, proj: Project):

    locals: dict[PackageId, ClassifiedUrl] = {}
    locals[proj.name.uncomment] = url_o

    for each in proj.locals:
        url = each.uncomment.url.uncomment
        branch = url.git_branch
        locals[each.uncomment.package.uncomment] = classify_url(
            url.link.uncomment, branch and branch.uncomment
        )

    return (
        locals,
        Metadata(
            proj.name,
            proj.authors,
            [Commented([], Dist(version=proj.version, url=None, deps=proj.deps))],
        ),
    )

