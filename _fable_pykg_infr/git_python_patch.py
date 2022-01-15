import git
import sys

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
