#!/usr/bin/env python3
"""Replay the E3 test selection under a sandbox that cannot write into 0o700 dirs.

Why this file exists (environment note, not a test change)
----------------------------------------------------------
In this DSH sandbox a directory created with POSIX mode ``0o700`` is created but
then refuses nested ``mkdir``/file writes (``PermissionError: [WinError 5]``):
``os.mkdir(d, 0o700)`` -> later ``os.mkdir(d/'sub')`` fails, while
``os.mkdir(d)`` / ``os.mkdir(d, 0o777)`` -> succeeds.  ``tempfile.mkdtemp()``
uses exactly ``0o700``, so *every* fixture that uses
``tempfile.TemporaryDirectory()`` errored out for environmental reasons before
reaching a single assertion.

This wrapper only replaces ``tempfile.mkdtemp`` with an equivalent that passes
``0o777``; it does not touch, skip, relax or reorder any test.  The same
selection runs unchanged on a normal host with

    python -B -m unittest discover -s audit/tests -p "test_tcb*.py" -v

Usage (from the e3 worktree):  python -B harness_e3_tests.py [start_dir]
"""

from __future__ import annotations

import os
import sys
import tempfile
import unittest

_candidates = tempfile._get_candidate_names  # name generator, version-stable


def _mkdtemp_permissive(suffix=None, prefix=None, dir=None):
    suffix = suffix or ""
    prefix = prefix or tempfile.gettempprefix()
    dir = dir or tempfile.gettempdir()
    for _ in range(10000):
        name = os.path.join(dir, prefix + next(_candidates()) + suffix)
        try:
            os.mkdir(name, 0o777)      # the only difference from tempfile
        except FileExistsError:
            continue
        except OSError:
            continue
        return name
    raise FileExistsError("no usable temporary directory name found")


tempfile.mkdtemp = _mkdtemp_permissive


def main(argv=None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    start = args[0] if args else "audit/tests"
    suite = unittest.TestLoader().discover(start, pattern="test_tcb*.py")
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
