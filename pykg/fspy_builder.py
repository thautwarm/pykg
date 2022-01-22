from __future__ import annotations
import typing
from pykg.component import SpecifierSet, operator, specifier

from pykg.data_reflection import from_comf, reflect
from pykg.project import Metadata, Project, Commented, Dep, Local, Author
from .version import Version as version
from .utils import to_netversion
from .async_request import areadpage, get_async_result
from pykg.fetch_dependencies import Requirements
from typing_extensions import Protocol
from pathlib import Path
from dataclasses import replace, dataclass
from urllib.parse import urlparse
from .classified_url import ClassifiedUrl, classify_url
from .utils import to_valid_identifier, to_posix
from .version import Version
from . import log
from . import git
from copy import deepcopy
from .xml import xml
import tomli_w

PackageId = str

PYKG_MODULES = Path("pykg_modules")


@reflect
@dataclass
class FableRepo:
    pkgname: str
    url: ClassifiedUrl
    src: list[str]


@reflect
@dataclass
class LockProject:
    pkgname: str
    pkgver: Version
    authors: list[Author]
    python_version: Version | None
    net_version: Version | None
    local_urls: list[tuple[PackageId, ClassifiedUrl]]
    pypi_deps: list[tuple[str, Version]]
    nuget_deps: list[tuple[str, Version]]
    fable_repos: list[FableRepo]
    python_package: str
    fs_python_package: str
    fsexe: str | None


class BuildError(Exception):
    pass


class FsPyBuilder:
    def __init__(self, requirements: Requirements):
        self.requirements = requirements

    def get_fspy_repo(self, meta: Metadata):
        pkg_name = meta.name.uncomment
        classified_url = self.requirements.locals.get(pkg_name)
        if not classified_url:
            dist = self.requirements.get_dist(meta)
            if not dist.url:
                raise BuildError(
                    f"invalid 'fspy' project {pkg_name} from {classified_url}; fspy project should always have a url in a distribution (not in project.comf, but in the generated metadata.comf)."
                )
            url = dist.url.uncomment
            classified_url = classify_url(
                url.link.uncomment, url.git_branch and url.git_branch.uncomment
            )
        return git.get_git_repo(
            classified_url, pkg_name == self.requirements.self_meta.name
        )

    def lock(self):
        requirements = self.requirements
        self_name = requirements.self_meta.name.uncomment
        self_proj = deepcopy(requirements.self_proj)

        if not self_proj:  # not a local project
            repo = self.get_fspy_repo(requirements.self_meta)
            resp, comf = get_async_result(repo.areadfile("project.comf"))
            if resp != 200:
                raise BuildError from ConnectionError(
                    f"{repo.url} does not contain a project.comf in the root."
                )
            self_proj = from_comf(Project, comf.decode("utf-8"))

        self_proj.deps = []
        self_proj.locals = []

        for pkgid, local in requirements.locals.items():
            self_proj.locals.append(
                Commented(
                    [], Local(Commented([], pkgid), Commented([], local.to_valid_url()))
                )
            )

        _, pypkgname = self_name.split("/")
        python_package = to_valid_identifier(pypkgname, ignore_dash=True)
        fable_python_package = python_package + "__fable"

        lock_proj = LockProject(
            pkgname=self_name,
            pkgver=self_proj.version.uncomment,
            authors=[author.uncomment for author in self_proj.authors],
            python_version=None,
            net_version=None,
            nuget_deps=[],
            local_urls=[],
            pypi_deps=[],
            fable_repos=[],
            fsexe=self_proj.exe and self_proj.exe.uncomment,
            python_package=python_package,
            fs_python_package=fable_python_package,
        )

        lock_proj.local_urls.extend(requirements.locals.items())

        for pkgid, (metadata, ver) in requirements.dependencies.items():
            kind, name = pkgid.split("/")

            if kind == "pypi":
                lock_proj.pypi_deps.append((name, ver))

            elif kind == "fspy":
                repo = self.get_fspy_repo(metadata)
                _, comf = repo.sync_readfile("project.comf")
                proj = from_comf(Project, comf.decode("utf-8"))
                sources = []
                for fsharp_src in proj.src.uncomment:
                    sources.append(fsharp_src.uncomment)
                lock_proj.fable_repos.append(FableRepo(pkgid, repo.url, sources))

            elif kind == "nuget":
                lock_proj.nuget_deps.append((name, ver))

            elif kind == "lang" and name == "python":
                lock_proj.python_version = ver

            elif kind == "lang" and name == "net":
                lock_proj.net_version = ver

        return lock_proj


def build_from_lock(lock_proj: LockProject, update: bool = False, **opts):
    pykg_modules = PYKG_MODULES
    pyproject_deps: list[tuple[str, dict]] = []

    python_requires = lock_proj.python_version
    python_requires = python_requires and python_requires.to_string_without_prefix()
    net_version = lock_proj.net_version
    net_version = net_version and to_netversion(net_version)
    fsharp_sources: list[str] = []

    for name, ver in lock_proj.pypi_deps:
        pyver = ver.to_string_without_prefix()
        if python_requires:
            pyproject_deps.append((name, dict(version=pyver, python=python_requires)))
        else:
            pyproject_deps.append((name, dict(version=pyver)))

    for fable_repo in lock_proj.fable_repos:
        repo = git.get_git_repo(fable_repo.url, fable_repo.pkgname == lock_proj.pkgname)
        for source in fable_repo.src:
            fsharp_sources.append(str(repo.resolve_path(pykg_modules, source)))
            repo.require_file(source)

    pkgname = lock_proj.pkgname.split("/")[1]

    poetry_toml = tomli_w.dumps(
        {
            "tool": {
                "poetry": {
                    "authors": [
                        f"{author.name.uncomment} {author.email or ''}"
                        for author in lock_proj.authors
                    ],
                    "description": "",
                    "version": lock_proj.pkgver.to_string_without_prefix(),
                    "dependencies": {k: v for k, v in pyproject_deps},
                    "name": pkgname,
                    "packages": [
                        {"include": lock_proj.python_package},
                        {"include": lock_proj.fs_python_package},
                    ],
                },
            }
        }
    )
    fsproj = (
        xml(
            name="Project",
            Sdk="Microsoft.NET.Sdk",
            content=[
                xml(
                    name="PropertyGroup",
                    content=[
                        xml(
                            name="TargetFramework",
                            content=opts.get("net_framework", net_version),
                        ),
                        xml(name="NoWarn", content="3370"),
                    ],
                ),
                xml(
                    name="ItemGroup",
                    content=[
                        xml(name="Compile", Include=src, content=None)
                        for src in fsharp_sources
                    ],
                ),
                xml(
                    name="ItemGroup",
                    content=[
                        xml(
                            name="PackageReference",
                            Include="Fable.Core.Experimental",
                            version=opts.get("fable_core_version", "4.0.0-alpha-029"),
                            content=None,
                        ),
                        *[
                            xml(
                                name="PackageReference",
                                Include=name,
                                version=to_netversion(ver),
                                content=None,
                            )
                            for name, ver in lock_proj.nuget_deps
                        ],
                    ],
                ),
            ],
        )
        .to_doc()
        .show()
    )

    Path(".").joinpath(f"pyproject.toml").write_text(poetry_toml, encoding='utf-8')
    Path(".").joinpath(f"{pkgname}.fsproj").write_text(fsproj, encoding='utf-8')

    if update:
        git.Git.update_(str(pykg_modules))

    path_o_pypack  = Path(lock_proj.python_package)

    # avoid Poetry error report
    if not path_o_pypack.exists():
        path_o_pypack.mkdir(exist_ok=True, parents=True, mode=0o777)
        (path_o_pypack / "__init__.py").write_text("", encoding='utf-8')
