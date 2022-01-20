from __future__ import annotations
from pykg.data_reflection import (
    reflect,
    reflect_opt,
    type_reflection,
    get_reflection_opts,
    from_comf,
    to_comf,
)
from pykg.component import CNum, CStr, Commented
from pykg.project import Project, Metadata
from pykg.fetch_dependencies import (
    get_deps_from_metadata,
    DEFAULT_MIRROR,
    get_deps_from_local_project,
)
from pykg.fspy_builder import FsPyBuilder, LockProject, build_from_lock
from pathlib import Path
from pykg import log
from wisepy2 import wise


def main(mirror: str = DEFAULT_MIRROR):
    path = "project.comf"
    proj = from_comf(Project, Path(path).read_text())
    req = get_deps_from_local_project(mirror, path, proj, {})
    lock_project = FsPyBuilder(req).lock()
    lps = to_comf(lock_project)
    print("format v0.1\n" + lps)
    from_comf(LockProject, "format v0.1\n" + lps)
    build_from_lock(lock_project, True)

if "__main__" == __name__:
    try:
        wise(main)()
    except Exception as e:
        log.error(str(e))
        raise

