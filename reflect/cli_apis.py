from wisepy2 import wise
from .builder import FsPyBuilder, build_from_lock
from __future__ import annotations
from reflect.data_reflection import (
    reflect,
    reflect_opt,
    type_reflection,
    get_reflection_opts,
    from_comf,
    to_comf,
)
from reflect.component import CNum, CStr, Commented
from reflect.project import Project, Metadata
from reflect.fetch_dependencies import (
    get_deps_from_metadata,
    DEFAULT_MIRROR,
    get_deps_from_local_project,
)
from reflect.builder import FsPyBuilder, LockProject, build_from_lock, PYKG_MODULES
from pathlib import Path
from reflect import log
from wisepy2 import wise
from subprocess import check_call
from distutils.spawn import find_executable
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
            Path("project.lock.comf").write_text("format v0.1\n" + lps)
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
    def _run_from_proj(lock_project: LockProject):
        if lock_project.fsexe:
            if python := find_executable("python"):
                check_call(
                    [
                        python,
                        "-c",
                        f"from {lock_project.fs_python_package}.local.{lock_project.fsexe} import main;main()",
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
        pykg._run_from_proj(lock_project)

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
        pykg._run_from_proj(lock_project)

def main():
    try:
        wise(pykg)()
    except Exception as e:
        log.error(str(e))
        sys.exit(1)
