from pykg.component import Commented, SpecifierSet, operator, specifier
from pykg.data_reflection import (
    from_comf,
    to_comf,
)
from pykg.project import Project, Dep
from pykg.fetch_dependencies import (
    DEFAULT_MIRROR,
    get_deps_from_local_project,
)
from pykg.fspy_builder import FsPyBuilder, LockProject, build_from_lock, PYKG_MODULES
from pykg.version import Version
from pykg.component import cmt
from pathlib import Path
from pykg import log
from wisepy2 import wise
from subprocess import check_call
from distutils.spawn import find_executable
from tempfile import mkstemp
import traceback
import sys


class pykg:
    @staticmethod
    def main(
        *,
        update: bool = False,
        mirror: str = DEFAULT_MIRROR,
        build: bool = False,
        external_build: bool = False,
        fable_core_version: str = "4.0.0-alpha-027",
    ):
        path = "project.comf"
        proj = from_comf(Project, Path(path).read_text())
        lock_path = Path("project.lock.comf")
        if update or not lock_path.exists():
            req = get_deps_from_local_project(mirror, path, proj, {})
            lock_project = FsPyBuilder(req).lock()
            lps = to_comf(lock_project)
            Path("project.lock.comf").write_text(
                "format v0.1\n" + lps, encoding="utf-8"
            )
        else:
            lock_project = from_comf(LockProject, lock_path.read_text())

        if update or build:
            pass
        else:
            return lock_project

        build_from_lock(lock_project, update, fable_core_version=fable_core_version)

        if not build or not external_build:
            return lock_project

        if fsexe := find_executable("fable-py"):
            fsargs = [fsexe, "--outDir", lock_project.fs_python_package]
        elif fsexe := find_executable("fable"):
            fsargs = [
                fsexe,
                "--outDir",
                lock_project.fs_python_package,
                "--lang",
                "Python",
            ]
        else:
            raise FileNotFoundError(
                "fable executables not found: try install fable-python via:\n"
                "    "
                f"'dotnet tool install --global fable-py --version {fable_core_version}' or greater"
            )

        if poetry_exe := find_executable("poetry"):
            if update:
                poetry_args = [poetry_exe, "install"]
            else:
                poetry_args = []
        else:
            raise FileNotFoundError(
                "poetry executables not found: try install poetry via:\n"
                "    "
                f"'pip install poetry'"
            )

        if fsargs:
            check_call(fsargs)

        if poetry_args:
            check_call(poetry_args)

        return lock_project

    @staticmethod
    def resolve(
        *, mirror: str = DEFAULT_MIRROR, fable_core_version: str = "4.0.0-alpha-027"
    ):
        """resolve dependencies and create new 'project.lock.comf'
        """
        pykg.main(
            update=True,
            mirror=mirror,
            build=False,
            external_build=False,
            fable_core_version=fable_core_version,
        )

    @staticmethod
    def build(
        *,
        resolve: bool = False,
        external: bool = True,
        mirror: str = DEFAULT_MIRROR,
        fable_core_version: str = "4.0.0-alpha-027",
    ):
        """build packages
        """
        pykg.main(
            update=resolve,
            mirror=mirror,
            build=True,
            external_build=external,
            fable_core_version=fable_core_version,
        )

    @staticmethod
    def lock(
        *,
        update: bool = False,
        mirror: str = DEFAULT_MIRROR,
        build: bool = False,
        external: bool = False,
        fable_core_version: str = "4.0.0-alpha-027",
    ):
        """create 'project.lock.comf' if not exists
        """
        pykg.main(
            update=update,
            mirror=mirror,
            build=build,
            external_build=external,
            fable_core_version=fable_core_version,
        )

    @staticmethod
    def __run_from_proj(lock_project: LockProject):
        if lock_project.fsexe:
            if python := find_executable("python"):
                check_call(
                    [
                        python,
                        "-c",
                        f"import {lock_project.fs_python_package}.{lock_project.fsexe}",
                    ]
                )
            else:
                log.error("'python' is not in the environment")
        else:
            log.error("'exe' field in project.toml not specified")

    @staticmethod
    def run(
        *,
        update: bool = False,
        mirror: str = DEFAULT_MIRROR,
        build: bool = False,
        external_build: bool = False,
        fable_core_version: str = "4.0.0-alpha-027",
    ):
        """
        in default, run without package resolution
        """
        lock_project = pykg.main(
            update=update,
            mirror=mirror,
            build=build,
            external_build=external_build,
            fable_core_version=fable_core_version,
        )
        pykg.__run_from_proj(lock_project)

    @staticmethod
    def a(*, mirror: str = DEFAULT_MIRROR, fable_core_version: str = "4.0.0-alpha-027"):
        """
        resolve, build, and run
        """
        lock_project = pykg.main(
            update=True,
            mirror=mirror,
            build=True,
            external_build=True,
            fable_core_version=fable_core_version,
        )
        pykg.__run_from_proj(lock_project)

    @staticmethod
    def new(proj_dir: str, *, force: bool = False):
        path_o_proj_dir = Path(proj_dir)
        package_name = "fspy/" + path_o_proj_dir.absolute().with_suffix("").name.strip()
        if path_o_proj_dir.exists():
            path_o_project = path_o_proj_dir / "project.comf"
            if path_o_project.exists():
                if not force:
                    log.warn(
                        f"there is a fable pykg project in {proj_dir}; add --force to overwrite it."
                    )
                    return
        else:
            path_o_proj_dir.mkdir(exist_ok=True, parents=True, mode=0o777)
            path_o_project = path_o_proj_dir / "project.comf"

        new_proj = Project(
            cmt(package_name),
            version=cmt(Version(0, 1, 0)),
            mirror=cmt(DEFAULT_MIRROR),
            authors=[],
            builder=None,
            locals=[],
            src=cmt([cmt("src/main.fs"),]),
            deps=[
                cmt(
                    Dep(
                        cmt("lang/python"),
                        cmt(
                            SpecifierSet(
                                frozenset(
                                    [specifier(operator.COMPACT, Version(3, 8, 0),)]
                                )
                            ),
                        ),
                    ),
                ),
                cmt(
                    Dep(
                        cmt("lang/net"),
                        cmt(
                            SpecifierSet(
                                frozenset(
                                    [
                                        specifier(operator.GE, Version(5, 0, 0),),
                                        specifier(operator.LT, Version(7, 0, 0),),
                                    ]
                                ),
                            ),
                        ),
                    ),
                ),
            ],
            exe=cmt("src.main"),
        )
        proj_str = to_comf(new_proj)

        path_o_project.write_text("format v0.1\n" + proj_str, encoding="utf-8")

        (path_o_proj_dir / ".gitignore").write_text(
            (Path(__file__).parent / "fspy_ignore.txt").read_text(encoding="utf-8"),
            encoding="utf-8",
        )

        (path_o_proj_dir / "src").mkdir(exist_ok=True, parents=True, mode=0o777)
        (path_o_proj_dir / "src" / "main.fs").write_text(
            "module Main\n\n"
            "let _ = printfn \"hello world\"\n")


def main():
    try:
        wise(pykg)()
    except Exception as e:
        log.error(str(e))
        _, tmpfile = mkstemp(suffix=".log", prefix="pykg_")
        log.error(f"full exception is stored in {tmpfile}")
        Path(tmpfile).write_text(traceback.format_exc(), encoding="utf-8")
        sys.exit(1)
