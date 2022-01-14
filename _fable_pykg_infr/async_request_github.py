from __future__ import annotations
from .async_request import (
    get_async_result,
    areadpage,
    run_many,
    gather_with_limited_workers,
)
from _fable_pykg.src.proj import parse_project
from . import log
from .version import get_typed_version
import git
import re
import typing
import sys

from _fable_pykg_infr import version

if sys.platform == 'win32':
    # https://stackoverflow.com/questions/60707687/how-to-skip-windows-credentials-manager-using-gitpython
    old__init__ = git.cmd.Git.__init__

    '''
    Method redefining ``__init__`` method of ``gitpy.cmd.Git``.

    The new definition wraps original implementation and adds
    "-c credential.helper=" to persistent git options so that
    it will be included in every git command call.
    '''
    def new__init__(self, *args, **kwargs):
        old__init__(self, *args, **kwargs)
        self._persistent_git_options = ["-c", "credential.helper="]


    '''Set __init__ implementation of gitpy.cmd.Git to that is implemented above'''
    git.cmd.Git.__init__ = new__init__

if typing.TYPE_CHECKING:
    from .comfig_require import Component

tag = re.compile('refs/tags/(v\S+)')

def request_github_package_versions(package_name: str):
    g = git.Git()
    url = rf"https://github.com/{package_name}"
    tags = []
    for ref in g.ls_remote(url).split('\n'):
        found = tag.findall(ref.split('\t')[-1].strip())
        if not found:
            continue
        tags.append(get_typed_version(found[0]))
    tags.reverse()
    return tags

def request_github_package_with_tag(package_name: str, tag: version) -> str:
    tag_str = str(tag)
    resp, v = yield from areadpage(rf"https://raw.githubusercontent.com/{package_name}/{tag_str}/fable-pykg.comf")
    if resp.status != 200:
        raise ConnectionError
    try:
        return parse_project(v.decode('utf-8'))
    except (SystemExit, KeyboardInterrupt):
        raise
    except Exception as e:
        log.error(f"invalid {package_name}/fable-pykg.comf:" + str(e))
        raise e
