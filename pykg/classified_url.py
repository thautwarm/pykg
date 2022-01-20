from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from urllib.parse import urlparse

from pykg.component import Commented
from .data_reflection import reflect, reflect_union
from .utils import to_posix, to_valid_identifier
import typing
import os

if typing.TYPE_CHECKING:
    def cache(x):
        return x
else:
    try:
        from functools import cache
    except ImportError:
        from functools import lru_cache
        cache = lru_cache(maxsize=None)

if typing.TYPE_CHECKING:
    ClassifiedUrl = typing.Union[
        'LocalProjUrl', 'CloudProjUrl', 'LocalMetaUrl', 'CloudMetaUrl', 'CloudGitRepoUrl',
    ]
    ClassifiedUrl_RT = object
else:
    @reflect_union
    class ClassifiedUrl:
        pass
    ClassifiedUrl_RT = ClassifiedUrl


@reflect
@dataclass(frozen=True)
class LocalProjUrl(ClassifiedUrl_RT):
    """it may be a git repo, but not a must
    """
    project_comf_path: str

    @cache
    def local_git_directory(self) -> str:
        path = self.project_comf_path[:-len("/project.comf")]
        if path == "":
            secs = ["local"]
        else:
            secs = to_posix("local_" + self.project_comf_path[:-len("/project.comf")]).split('/')
        return '/'.join(map(to_valid_identifier, secs)).replace('//', '/mod/')

    def get_project_dir(self):
        return os.path.dirname(self.project_comf_path)

    def cast(self) -> ClassifiedUrl:
        return self

    def allow_virtual_git(self):
        return True

    def __repr__(self):
        return f'<local project ({self.project_comf_path})>'

    def to_valid_url(self):
        from .project import Url
        return Url(Commented([], self.project_comf_path))


@reflect
@dataclass(frozen=True)
class CloudProjUrl(ClassifiedUrl_RT):
    project_comf_url: str

    @cache
    def local_git_directory(self) -> str:
        result = urlparse(self.project_comf_url[:-len("/project.comf")])
        hostname = result.hostname or 'NO_HOST'
        path = result.path
        secs = to_posix(os.path.join("unknown_cloud", hostname, path)).split('/')
        return '/'.join(map(to_valid_identifier, secs))

    def get_project_dir_url(self):
        return os.path.dirname(self.project_comf_url)

    def cast(self) -> ClassifiedUrl:
        return self

    def allow_virtual_git(self):
        return True

    def __repr__(self):
        return f'<cloud project ({self.project_comf_url})>'

    def to_valid_url(self):
        from .project import Url
        return Url(Commented([], self.project_comf_url))


@reflect
@dataclass(frozen=True)
class LocalMetaUrl(ClassifiedUrl_RT):
    meta_comf_path: str

    def local_git_directory(self) -> str:
        raise NotImplementedError

    def cast(self) -> ClassifiedUrl:
        return self

    def allow_virtual_git(self):
        return False

    def __repr__(self):
        return f'<local metadata ({self.meta_comf_path})>'

    def to_valid_url(self):
        from .project import Url
        return Url(Commented([], self.meta_comf_path))

@reflect
@dataclass(frozen=True)
class CloudMetaUrl(ClassifiedUrl_RT):
    link: str

    def local_git_directory(self) -> str:
        raise NotImplementedError

    def cast(self) -> ClassifiedUrl:
        return self

    def allow_virtual_git(self):
        return False

    def __repr__(self):
        return f'<cloud metadata ({self.link})>'

    def to_valid_url(self):
        from .project import Url
        return Url(Commented([], self.link))

@reflect
@dataclass(frozen=True)
class CloudGitRepoUrl(ClassifiedUrl_RT):
    provider: str  # github, gitlab, bitbucket
    user_repo: str  # user/repo
    branch: str

    @cache
    def local_git_directory(self) -> str:
        secs = to_posix(os.path.join(self.provider, self.user_repo, self.branch)).split('/')
        return '/'.join(map(to_valid_identifier, secs))

    def cast(self) -> ClassifiedUrl:
        return self

    def allow_virtual_git(self):
        return True

    def __repr__(self):
        return f'cloud git repo ({self.provider}:{self.user_repo}) branch {self.branch}'

    def to_valid_url(self):
        if self.provider == 'github':
            link = f"https://{self.provider}.com/{self.user_repo}"
        elif self.provider == 'gitlab':
            link = f"https://{self.provider}.com/{self.user_repo}"
        elif self.provider == 'bitbucket':
            link = f"https://{self.provider}.com/{self.user_repo}"
        else:
            raise Exception(f"unknown provider {self.provider}.")
        from .project import Url
        return Url(Commented([], link), Commented([], self.branch))




RawUrlIfTheHostIsNotRaw = str
HostName = str
ProviderName = str
GIT_HOST_PROVIDERS: dict[HostName, ProviderName] = {
    "github.com": "github",
    "gitlab.com": "gitlab",
    "bitbucket.com": "bitbucket.org",
}

@cache
def classify_url(x: str, branch: str | None):
    if x.startswith("https://") or x.startswith("http://"):
        result = urlparse(x)
        host = result.hostname or ""
        if provider := GIT_HOST_PROVIDERS.get(host):
            secs = list(filter(None, result.path.split("/")))
            if len(secs) == 2:
                # is repo
                branch = branch or "main"
                return CloudGitRepoUrl(provider, to_posix(os.path.join(*secs)), branch).cast()

            if provider == "github":  # rawgithub use different hostname:
                raise FileNotFoundError(
                    f"invalid raw link ({x}) to GitHub project.comf;"
                    r"the hostname of a GitHub rawlink should be 'raw.githubusercontent.com'."
                )

        if result.path.endswith("/project.comf"):
            return CloudProjUrl(x).cast()

        if result.path.endswith(".meta.comf"):
            return CloudMetaUrl(x).cast()

        raise FileNotFoundError(
            f"invalid url {x}: should link to a 'project.comf' or 'xxx.meta.comf',"
            f" or directly refer to a Git repo root like 'https://github.com/<user>/<repo>'."
        )

    if x.startswith("file:///"):
        x = x[len("file:///") :]

    path_x = Path(Path(x).as_posix())

    if path_x.is_file() and path_x.name == "project.comf":
        return LocalProjUrl(x).cast()

    if path_x.is_dir() and (path_x / "project.comf").exists():
        return LocalProjUrl(os.path.join(x, "project.comf")).cast()

    if x.endswith(".meta.comf"):
        return LocalMetaUrl(x).cast()

    raise FileNotFoundError(
        "invalid path {x}: should be a path to `project.comf` or `xxx.meta.comf`."
    )

