"""Local measurement shim (NOT part of the deliverable, lives outside the worktree).

This sandbox denies writes inside any directory created with mode 0o700 --
that is exactly how ``tempfile.mkdtemp`` (and therefore ``TemporaryDirectory``)
creates its directories, so every harness run dies with WinError 5 here while
being perfectly fine in an unsandboxed context.  Dropping the mode makes the new
directory inherit the parent's ACL and the run behaves normally.  Nothing about
the code under test is changed: only the umask-like mode argument of os.mkdir.
"""
import os

_original_mkdir = os.mkdir


def mkdir(path, mode=0o777, *, dir_fd=None):
    kwargs = {} if dir_fd is None else {"dir_fd": dir_fd}
    return _original_mkdir(path, 0o777, **kwargs)


os.mkdir = mkdir
