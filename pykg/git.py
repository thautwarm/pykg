from __future__ import annotations
from .async_request import (
    areadpage,
    create_file_url,
    get_async_result,
    gather_with_limited_workers,
    run_many,
)
from dulwich.repo import MemoryRepo
from dulwich.client import HttpGitClient, HTTPUnauthorized
from dulwich.errors import NotGitRepository
from .classified_url import *
from urllib.parse import urljoin
from pathlib import Path
from . import log
import diskcache
import os
import re
import typing

if typing.TYPE_CHECKING:

    def cache(x):
        return x
else:
    try:
        from functools import cache
    except ImportError:
        from functools import lru_cache
        cache = lru_cache(maxsize=None)


_version_regex = re.compile(
    "^\s*v?(?P<major>\d+)(\.(?P<minor>\d+)(\.(?P<micro>\d+))?)?\s*$"
)


def github_file_path(user_repo: str, path: str, branch: str = "main"):
    return f"https://raw.githubusercontent.com/{user_repo}/{branch}/{path}"


def gitlab_file_path(user_repo: str, path: str, branch: str = "main"):
    return f"https://gitlab.com/{user_repo}/-/raw/{branch}/{path}"


def bitbucket_file_path(user_repo: str, path: str, branch: str = "main"):
    return f"https://bitbucket.org/{user_repo}/raw/{branch}/{path}"


_provider_apis: dict[str, tuple[str, typing.Callable[[str, str, str], str]]] = {
    "github": ("https://github.com", github_file_path),
    "bitbucket": ("https://bitbucket.org", bitbucket_file_path),
    "gitlab": ("https://gitlab.com", gitlab_file_path),
}


@cache
def get_git_repo(classified_url: ClassifiedUrl, is_me: bool):
    return Git(classified_url, is_me)


CACHE_PATH = os.path.expanduser("~/.pykg-cache")
FILES: typing.Type[dict[str, str]]
HEAD = bytes
BRNACHED_FILES: typing.Type[dict[HEAD, FILES]]
REFS: typing.Type[dict[HEAD, bytes]]


class _CACHE_TYPE:
    def __init__(self, dc):
        self._dc = dc
        self.mem = {}

    def _sync_from_disk(self, k, default):
        v = self.mem[k] = self._dc.get(k, default)
        return v

    def get_refs(self, url: str) -> REFS:
        key = "url@@" + url
        if key in self.mem:
            return self.mem[key]
        return self._sync_from_disk(key, {})

    def set_refs(self, url: str, refs: REFS) -> REFS | None:
        key = "url@@" + url
        self.mem[key] = refs

    def get_files(self, url: str, head: bytes) -> dict[str, str]:
        key = "files@@" + url
        if key not in self.mem:
            branched_files: dict = self._sync_from_disk(key, {})
        else:
            branched_files: dict = self.mem[key]
        branched_files.setdefault(head, set())
        return typing.cast("FILES", branched_files[head])

    def set_files(self, url: str, head: bytes, files: dict[str, str]):
        branched_files = self.get_files(url, head)
        key = "files@@" + url
        if key not in self.mem:
            branched_files = self._sync_from_disk(key, {})
        else:
            branched_files = self.mem[key]
        branched_files[head] = files

    def dump_disk_(self):
        # should only be called after NEED_UPDATE tasks are executed
        for k, v in self.mem.items():
            self._dc[k] = v


GLOBAL_CACHE = _CACHE_TYPE(diskcache.Cache(CACHE_PATH))
NEED_UPDATE: list[typing.Callable[[str], typing.Generator]] = []


class Git:
    """Virtual git repo.
    NOTE: Do not use construct it directly, instead, use 'get_git_repo'!
    - classified_url: A ClassifiedUrl; if provider is specified in the url, it is a cloud host; otherwise, it is a local repo.
    - is_me: is this repo the current project.
    """

    def __init__(self, classified_url: ClassifiedUrl, is_me: bool = False):
        self.is_me = is_me
        self.url = classified_url
        local_tracked_files: set[str] = set()
        self.is_git = False
        self.local_tracked_files: set[str] = local_tracked_files

        if isinstance(classified_url, LocalProjUrl):
            self._local_git_dir = classified_url.local_git_directory()
            self._setup_local(classified_url)

        elif isinstance(classified_url, CloudProjUrl):
            self._local_git_dir = classified_url.local_git_directory()
            self._setup_nonlocal(classified_url)

        elif isinstance(classified_url, CloudGitRepoUrl):
            self._local_git_dir = classified_url.local_git_directory()
            self.is_git = True
            self._setup_git_repo(classified_url)

        else:
            raise ConnectionError(f"{classified_url} is not processed as a git repo!")

    def _setup_git_repo(self, classified_url: CloudGitRepoUrl):
        provider = classified_url.provider
        assert provider in (
            "github",
            "gitlab",
            "bitbucket",
        ), f"Git host <{provider}> are not supported yet!"
        user_repo = classified_url.user_repo
        root, _provider_api_get_file_path = _provider_apis[provider]
        branch = classified_url.branch

        def _get_file(path: str):
            return _provider_api_get_file_path(user_repo, path, branch)

        self._get_file = _get_file
        url = root + "/" + user_repo
        remote_repo = HttpGitClient(url)
        local_repo = MemoryRepo()
        try:
            refs: dict[bytes, bytes] = remote_repo.fetch(url, local_repo).refs
        except NotGitRepository:
            raise NotGitRepository(
                f"{self.url!r} has invalid repo url: {url!r} is not git repo."
            )
        except HTTPUnauthorized:
            raise FileNotFoundError(
                f"Repo address {url!r} is not available, check if it's public or the name is incorrect."
            )

        stored_refs = GLOBAL_CACHE.get_refs(url)
        if _version_regex.match(branch):
            head = f"refs/tags/{branch}".encode("utf-8")
        else:
            head = f"refs/heads/{branch}".encode("utf-8")

        if head not in refs:
            raise FileNotFoundError(
                f"invalid git branch {branch} for {user_repo} from {provider}."
            )

        def _load_file(path: str):
            files = GLOBAL_CACHE.get_files(url, head)
            files[path] = ""

        self._load_file = _load_file

        def update_func(pykg_module_path):
            local_repo = MemoryRepo()
            refs: dict[bytes, bytes] = remote_repo.fetch(url, local_repo).refs
            stored_refs = GLOBAL_CACHE.get_refs(url)
            if head not in refs:
                try:
                    del stored_refs[head]
                except KeyError:
                    pass
                GLOBAL_CACHE.set_files(url, head, {})
                return
            stored_refs[head] = refs[head]
            files = GLOBAL_CACHE.get_files(url, head)

            def async_task(path: str):
                resp, file = yield from self.areadfile(path)
                if resp.status != 200:
                    log.warn(f"{path} not found from {self.url}")
                    return path, None
                return path, file.decode("utf-8")

            results = yield gather_with_limited_workers(
                [async_task(path) for path in files.keys()]
            )
            pykg_modules = Path(pykg_module_path)
            for path, newfile in results:
                path_o = self.resolve_path(pykg_modules, path)
                if newfile is None:
                    # TODO: delete local files
                    del files[path]
                else:
                    files[path] = newfile
                    path_o.parent.mkdir(exist_ok=True, parents=True, mode=0o777)
                    path_o.write_text(newfile, encoding='utf-8')

        if head not in stored_refs:
            stored_refs[head] = refs[head]
            GLOBAL_CACHE.set_refs(url, {head: refs[head]})
            NEED_UPDATE.append(update_func)
        else:
            assert isinstance(stored_refs, dict)
            if stored_refs.get(head, b"_not_found_stored") != refs.get(
                head, b"_not_found_fetch"
            ):
                NEED_UPDATE.append(update_func)

    def _setup_local(self, classified_url: LocalProjUrl):
        project_dir = classified_url.get_project_dir()

        def _get_file(path: str):
            return create_file_url(os.path.join(project_dir, path))

        def _load_file(path: str):
            norm_path = Path(path).as_posix()
            if norm_path not in self.local_tracked_files:
                self.local_tracked_files.add(norm_path)

        self._get_file = _get_file
        self._load_file = _load_file

        def update(pykg_module_path: str):
            pykg_module = Path(pykg_module_path)
            for path in self.local_tracked_files:
                path_o = self.resolve_path(pykg_module, path)
                resp, file_content = yield from self.areadfile(path)
                if resp.status == 200:
                    path_o.parent.mkdir(exist_ok=True, parents=True, mode=0o777)
                    with path_o.open("wb") as fr:
                        fr.write(file_content)
                else:
                    log.warn(f"{path} not found from {self.url}")

        NEED_UPDATE.append(update)

    def _setup_nonlocal(self, classified_url: CloudProjUrl):
        project_dir_url = classified_url.get_project_dir_url()

        def _get_file(path: str):
            return urljoin(project_dir_url, path)

        def _load_file(path: str):
            norm_path = Path(path).as_posix()
            if norm_path not in self.local_tracked_files:
                self.local_tracked_files.add(norm_path)

        self._get_file = _get_file
        self._load_file = _load_file

        def update(pykg_module_path: str):
            pykg_modules = Path(pykg_module_path)

            def async_task(path):
                path_o = self.resolve_path(pykg_modules, path)
                resp, file_content = yield from self.areadfile(path)
                if resp.status == 200:
                    path_o.parent.mkdir(exist_ok=True, parents=True, mode=0o777)
                    with path_o.open("wb") as fr:
                        fr.write(file_content)
                else:
                    log.warn(f"{path} not found from {self.url}")

            tasks = [async_task(path) for path in self.local_tracked_files]
            yield from gather_with_limited_workers(tasks)

        NEED_UPDATE.append(update)

    def areadfile(self, path: str):
        url = self._get_file(path)
        return (yield from areadpage(url))

    def sync_readfile(self, path: str):
        return get_async_result(self.areadfile(path))

    def require_file(self, path: str):
        self._load_file(path)

    @staticmethod
    def update_(pykg_module: str):
        run_many([each(pykg_module) for each in NEED_UPDATE])
        GLOBAL_CACHE.dump_disk_()

    def resolve_path(self, pykg_modules: Path, path: str):
        if self.is_me:
            return Path(path)

        return pykg_modules / self._local_git_dir / path
