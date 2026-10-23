"""E1: a failed required contract probe must fail the mutation CLI (review R2/P2).

The reviewer's reproduction (``reviews/4841271-acceptance/astra/reproduce_mutation_exit.py``)
measured the defect this file exists for: ``mutation_harness.run()`` hard-checked
only the two baseline probes, so ``fact_tree_removal``, ``unpin_entry`` and
``clean_checkout_head`` could report ``ok=False`` while the independent CLI still
exited 0 with ``violations=[]``.

The contract under test -- the frozen oracle -- is:

    every required contract probe failure causes a nonzero final CLI exit and
    names the failure; an unchanged valid baseline still passes.

The M1-M8 matrix is *not* changed by this task: its expected catches and its
documented expected blind spots are only read here, never relaxed.  Each case
below therefore asserts the CLI-level outcome only, and each failure mode is
injected as narrowly as possible.

Cost and exit status (round-2 repair).  The round-1 replay printed every case and
then never returned a usable exit status: seven cases each paid for the whole
M1-M8 matrix *and* for every health probe (~100-170 s here), which overran the
reviewer's 150 s budget, and the subprocess it was captured with inherited its
stdout/stderr pipes into grandchildren, so ``subprocess.run(timeout=...)`` spent
another ~445 s waiting for pipes that the direct child's death did not close.
Two things changed, neither of which touches an assertion:

* the M1-M8 matrix runs once, in the baseline case.  The healthy probes run once
  for real there too; the focused failure cases reuse those recorded results
  (``--reuse-probes``) after the harness re-checks that the repository bytes are
  still the same, and they run the injected probe for real.  A probe reported as
  reused is never executed again but keeps full standing in the exit contract.
* the no-argument entry point supervises the cases in a child process whose
  streams are *files*, not pipes, under one hard wall-clock deadline.  On expiry
  it kills the whole process tree (``taskkill /T`` on Windows) with a bounded
  grace and exits 124, so the total timeout also covers process cleanup.  A
  grandchild that keeps an inherited pipe open can therefore no longer stall the
  exit -- which is what the round-1 replay actually measured.

Entry points:

    python -B audit/tests/test_mutation_probe_exit.py            # supervised, all cases
    python -B audit/tests/test_mutation_probe_exit.py <CASE_ID>  # supervised, that case
    python -B audit/tests/test_mutation_probe_exit.py --total-seconds 60   # other budget
    python -B audit/tests/test_mutation_probe_exit.py --list     # case ids
    python -B audit/tests/test_mutation_probe_exit.py --in-process [<CASE_ID> ...]
    python -B audit/tests/test_mutation_probe_exit.py --self-test-timeout
    python -B -m unittest discover -s audit/tests -p "test_*.py"  # whole suite

``--self-test-timeout`` is the regression test for the round-1 exit failure: it
supervises a synthetic run that spawns a grandchild holding the inherited handles
and never finishes, and asserts that the supervisor still returns inside its
budget, reports 124, and reaped the grandchild.
"""
from __future__ import annotations

import contextlib
import ctypes
import io
import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import traceback
import unittest
from pathlib import Path

AUDIT = Path(__file__).resolve().parents[1]
if str(AUDIT) not in sys.path:
    sys.path.insert(0, str(AUDIT))
sys.dont_write_bytecode = True

import mutation_harness as mh  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]
CASE_IDS = (
    "E1.baseline_pass",
    "E1.fact_tree_removal_regression",
    "E1.unpin_entry_failure",
    "E1.clean_checkout_failure",
    "E1.baseline_failure",
    "E1.probe_exception",
    "E1.malformed_probe_result",
)

CHECKOUT_FAILURE = "fatal: not a git repository (or any parent up to mount point)"

#: one deadline for the whole supervised replay, cleanup included; the reviewed
#: budget for this replay is 150 s, so this leaves room for the kill grace below
DEFAULT_TOTAL_SECONDS = 120.0
#: how long the supervisor may spend killing and reaping the child tree
KILL_GRACE_SECONDS = 10.0
#: exit status for "the replay did not finish inside its own deadline"
TIMEOUT_EXIT = 124

#: probe results the baseline case recorded, reused by the focused cases
RECORDED = {"probes": None, "witness": None}


# ---------------------------------------------------------------------------
# helpers: drive the real CLI, inject one probe outcome, read the report
# ---------------------------------------------------------------------------
def _cli(argv=("--json", "--probes-only")):
    """Run the module's real CLI in-process: ``(exit_code, report, stdout, stderr)``."""
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = mh.main(list(argv))
    text = out.getvalue()
    try:
        report = json.loads(text)
    except json.JSONDecodeError:
        report = None
    return code, report, text, err.getvalue()


def _record(report):
    """Keep the baseline's real probe results for the focused cases to reuse."""
    RECORDED["probes"] = {name: {key: value for key, value in cell.items()
                                 if key != "reused"}
                          for name, cell in report["probes"].items()}
    RECORDED["witness"] = mh.repo_witness()


@contextlib.contextmanager
def _reuse_argv(excluded):
    """argv for a CLI run that reuses the baseline's healthy probes.

    Only probes named in ``excluded`` (the ones this case injects, and therefore
    must run for real) are left out.  When no baseline was recorded -- a single
    case replayed on its own -- every probe runs for real instead, so the case is
    never weaker than the standalone replay.
    """
    recorded = RECORDED["probes"] or {}
    probes = {name: cell for name, cell in recorded.items() if name not in excluded}
    if not probes or RECORDED["witness"] is None:
        yield ("--json", "--probes-only")
        return
    with tempfile.TemporaryDirectory(prefix="e1_reuse_") as holder:
        path = Path(holder) / "probes.json"
        path.write_text(json.dumps({"repo_witness": RECORDED["witness"],
                                    "probes": probes}, ensure_ascii=False),
                        encoding="utf-8")
        yield ("--json", "--probes-only", "--reuse-probes", str(path))


@contextlib.contextmanager
def _probe_outcomes(**stubs):
    """Replace the *outcome* of named probes for the duration of one CLI run.

    ``mh.PROBES`` is the module's own dispatch table; every probe that is not
    named still runs for real, and the table is restored even if the run raises.
    A probe in ``mh.REPO_ONLY_PROBES`` is called without a copy tree, so its
    stand-in takes no arguments.
    """
    saved = mh.PROBES
    mh.PROBES = tuple((name, stubs[name]) if name in stubs else (name, probe)
                      for name, probe in saved)
    try:
        yield
    finally:
        mh.PROBES = saved


def _report(code, report, stderr, case):
    assert report is not None, (
        f"{case}: the CLI printed no parseable JSON report (exit {code}); "
        f"stderr: {stderr.strip()[-500:]}")
    return report


def _named(report, probe):
    return [violation for violation in report["violations"] if probe in violation]


def _assert_probe_is_named(report, probe):
    named = _named(report, probe)
    assert named, (f"the failing probe {probe!r} is not named in "
                   f"violations={report['violations']}")
    return named


def _assert_probe_ran(report, probe):
    """A probe this case injects must have run for real, not been reused."""
    reused = report.get("probes_reused") or []
    assert probe not in reused, (
        f"{probe!r} is the probe this case injects, so it must run for real; the "
        f"report instead claims it was reused: {reused}")


def _assert_only_this_probe_failed(report, probe):
    others = {name: cell.get("detail") for name, cell in report["probes"].items()
              if name != probe and cell.get("ok") is not True}
    assert not others, (f"only {probe!r} was injected as failing, but {others} "
                        f"did not pass either")
    stray = [violation for violation in report["violations"] if probe not in violation]
    assert not stray, (f"a nonzero exit must be attributable to {probe!r}; other "
                       f"violations: {stray}")


# ---------------------------------------------------------------------------
# case 1: the valid baseline still passes (the "must not reject everything" side)
# ---------------------------------------------------------------------------
def case_baseline_pass():
    """Untouched repository: every required probe and M1-M8 pass once."""
    code, report, _, stderr = _cli(("--json",))
    _report(code, report, stderr, "E1.baseline_pass")
    assert code == 0, (f"the valid baseline must exit 0, got {code}; "
                       f"violations={report['violations']}")
    assert report["exit_code"] == 0, report["exit_code"]
    assert report["violations"] == [], report["violations"]
    assert report["repository_unchanged"] is True
    assert tuple(report["probes"]) == tuple(name for name, _ in mh.PROBES)
    assert report["matrix_complete"] is True
    assert len(report["matrix"]) == len(mh.MUTATIONS)
    assert report["probes_reused"] == [], report["probes_reused"]
    failing = {name: cell.get("detail") for name, cell in report["probes"].items()
               if cell.get("ok") is not True}
    assert not failing, f"probes must pass on the untouched repository: {failing}"
    # Every required probe really ran here; the focused cases may reuse these.
    _record(report)


# ---------------------------------------------------------------------------
# case 2: the reviewer's real counterexample (Kept, not weakened)
# ---------------------------------------------------------------------------
def case_fact_tree_removal_regression():
    """Reproduce the reviewer's counterexample without editing any file.

    ``freshness.validate_project`` is wrapped in memory so that *only* the real
    target-set/admission rejection is swallowed (exactly the bypass used in
    ``reviews/4841271-acceptance/astra/reproduce_mutation_exit.py``).  Both
    baselines and the fact-tree probe run for real *under the bypass* here -- this
    case never reuses recorded results, because "the baselines still pass" has to
    be observed inside the patched run.  Before the fix this run ended with
    ``fact_tree_removal.ok=false``, ``violations=[]`` and ``exit_code=0``.
    """
    original = mh.freshness.validate_project
    original_tempdir = mh.tempfile.tempdir
    scratch = tempfile.mkdtemp(prefix="e1_mutation_scratch_")
    mh.tempfile.tempdir = scratch

    def regressed_admission_gate(base, deep=True):
        try:
            return original(base, deep=deep)
        except RuntimeError as error:
            if "not fully admitted, or stale target set" in str(error):
                return {}, {}
            raise

    try:
        with mh._patched(mh.freshness, validate_project=regressed_admission_gate):
            code, report, _, stderr = _cli()
    finally:
        mh.tempfile.tempdir = original_tempdir
        shutil.rmtree(scratch, ignore_errors=True)

    _report(code, report, stderr, "E1.fact_tree_removal_regression")
    assert report["probes_reused"] == [], (
        "this case must observe the baselines inside the patched run, so it may "
        f"not reuse recorded probe results: {report['probes_reused']}")
    probe = report["probes"]["fact_tree_removal"]
    assert probe.get("ok") is False, (
        "the injected freshness regression did not make fact_tree_removal fail, so "
        f"the reviewer's counterexample was not reproduced; probe={probe}")
    for name in ("baseline_bridge", "baseline_main"):
        assert report["probes"][name].get("ok") is True, (
            f"the injected bypass must leave {name} passing; "
            f"probe={report['probes'][name]}")
    assert code != 0, (
        "the final CLI exited 0 while a required contract probe failed (R2/P2); "
        f"probe={probe}, violations={report['violations']}")
    assert report["exit_code"] != 0, report["exit_code"]
    _assert_probe_is_named(report, "fact_tree_removal")
    assert len(report["violations"]) == 1, (
        "exactly the injected probe failure should be reported, so the nonzero "
        f"exit is attributable to it: {report['violations']}")


# ---------------------------------------------------------------------------
# cases 3 and 4: one contract probe per case, as required by the contract
# ---------------------------------------------------------------------------
def case_unpin_entry_failure():
    """``unpin_entry`` reporting failure must make the CLI nonzero and name it."""
    def failing(tmp=None):
        return {"ok": False, "detail": "unpinning an entry was reported as drift"}

    with _reuse_argv({"unpin_entry"}) as argv, _probe_outcomes(unpin_entry=failing):
        code, report, _, stderr = _cli(argv)
    _report(code, report, stderr, "E1.unpin_entry_failure")
    assert report["probes"]["unpin_entry"]["ok"] is False
    _assert_probe_ran(report, "unpin_entry")
    assert code != 0, (f"the final CLI exited 0 while unpin_entry failed; "
                       f"violations={report['violations']}")
    _assert_probe_is_named(report, "unpin_entry")
    _assert_only_this_probe_failed(report, "unpin_entry")
    assert report["matrix_complete"] is False


class _FailedCheckout:
    returncode = 1
    stdout = ""
    stderr = CHECKOUT_FAILURE + "\n"


class _NoGitSubprocess:
    """Stands in for ``subprocess`` the way a git-less archive fails the gate."""

    @staticmethod
    def run(*args, **kwargs):
        return _FailedCheckout()


def case_clean_checkout_failure():
    """``clean_checkout_head`` failing must make the CLI nonzero and name it.

    The injection replaces the module's ``subprocess`` seam only, so the probe's
    own code runs and reports the failure the reviewer saw on an archive without
    ``.git`` (``exit 1`` from ``bridges/check_clean_checkout.py``).
    """
    saved = mh.subprocess
    mh.subprocess = _NoGitSubprocess
    try:
        with _reuse_argv({"clean_checkout_head"}) as argv:
            code, report, _, stderr = _cli(argv)
    finally:
        mh.subprocess = saved
    _report(code, report, stderr, "E1.clean_checkout_failure")
    probe = report["probes"]["clean_checkout_head"]
    assert probe["ok"] is False, probe
    _assert_probe_ran(report, "clean_checkout_head")
    assert CHECKOUT_FAILURE in probe["detail"], probe["detail"]
    assert code != 0, (f"the final CLI exited 0 while clean_checkout_head failed; "
                       f"violations={report['violations']}")
    _assert_probe_is_named(report, "clean_checkout_head")
    _assert_only_this_probe_failed(report, "clean_checkout_head")


# ---------------------------------------------------------------------------
# cases 5-7: no probe outcome may be reported as success
# ---------------------------------------------------------------------------
def case_baseline_failure():
    """A failing baseline must be reported, not silently tolerated."""
    def failing(tmp=None):
        return {"ok": False, "detail": "an unmutated copy already fails a gate"}

    with _reuse_argv({"baseline_bridge", "baseline_main"}) as argv, \
            _probe_outcomes(baseline_bridge=failing, baseline_main=failing):
        code, report, _, stderr = _cli(argv)
    _report(code, report, stderr, "E1.baseline_failure")
    for name in ("baseline_bridge", "baseline_main"):
        assert report["probes"][name]["ok"] is False, report["probes"][name]
        _assert_probe_ran(report, name)
        _assert_probe_is_named(report, name)
    assert code != 0, (f"a failing baseline was reported as success; "
                       f"violations={report['violations']}")


def case_probe_exception():
    """A probe that raises must become a reported failure, not a pass or a crash."""
    def exploding(tmp=None):
        raise RuntimeError("synthetic probe explosion (E1.probe_exception)")

    with _reuse_argv({"unpin_entry"}) as argv, _probe_outcomes(unpin_entry=exploding):
        code, report, _, stderr = _cli(argv)
    _report(code, report, stderr, "E1.probe_exception")
    assert code != 0, ("a probe that raised was reported as success; "
                       f"violations={report['violations']}")
    assert report["exit_code"] != 0
    assert report["probes"]["unpin_entry"]["ok"] is False
    _assert_probe_ran(report, "unpin_entry")
    named = _assert_probe_is_named(report, "unpin_entry")
    joined = " ".join(named)
    assert "RuntimeError" in joined, joined
    assert "synthetic probe explosion" in joined, joined


def case_malformed_probe_result():
    """A result without a boolean ``ok`` is a failure, never silence."""
    def no_verdict(tmp=None):
        return {"detail": "looks fine, but no verdict field"}

    def not_a_mapping():
        return None

    with _reuse_argv({"unpin_entry", "clean_checkout_head"}) as argv, \
            _probe_outcomes(unpin_entry=no_verdict, clean_checkout_head=not_a_mapping):
        code, report, _, stderr = _cli(argv)
    _report(code, report, stderr, "E1.malformed_probe_result")
    assert code != 0, ("malformed probe results were reported as success; "
                       f"violations={report['violations']}")
    assert report["probes"]["unpin_entry"]["ok"] is False
    assert report["probes"]["clean_checkout_head"]["ok"] is False
    for name in ("unpin_entry", "clean_checkout_head"):
        _assert_probe_ran(report, name)
    named = _assert_probe_is_named(report, "unpin_entry")
    assert any("no boolean 'ok'" in violation for violation in named), named
    named = _assert_probe_is_named(report, "clean_checkout_head")
    assert any("NoneType" in violation for violation in named), named


CASES = {
    "E1.baseline_pass": case_baseline_pass,
    "E1.fact_tree_removal_regression": case_fact_tree_removal_regression,
    "E1.unpin_entry_failure": case_unpin_entry_failure,
    "E1.clean_checkout_failure": case_clean_checkout_failure,
    "E1.baseline_failure": case_baseline_failure,
    "E1.probe_exception": case_probe_exception,
    "E1.malformed_probe_result": case_malformed_probe_result,
}
assert tuple(CASES) == CASE_IDS, "case ids must match the frozen contract"


# ---------------------------------------------------------------------------
# discovery entry: one method per case id, asserting the same thing
# ---------------------------------------------------------------------------
class ProbeExitContract(unittest.TestCase):
    """One case per frozen id; a discovery run asserts what a replay asserts."""

    def test_E1_baseline_pass(self):
        case_baseline_pass()

    def test_E1_fact_tree_removal_regression(self):
        case_fact_tree_removal_regression()

    def test_E1_unpin_entry_failure(self):
        case_unpin_entry_failure()

    def test_E1_clean_checkout_failure(self):
        case_clean_checkout_failure()

    def test_E1_baseline_failure(self):
        case_baseline_failure()

    def test_E1_probe_exception(self):
        case_probe_exception()

    def test_E1_malformed_probe_result(self):
        case_malformed_probe_result()


# ---------------------------------------------------------------------------
# supervisor: one hard wall-clock deadline, file-backed streams, tree cleanup
# ---------------------------------------------------------------------------
def _child_env():
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def _pid_alive(pid):
    """True when ``pid`` still names a live process (no dependency beyond stdlib)."""
    if sys.platform == "win32":
        import ctypes

        kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
        kernel32.OpenProcess.restype = ctypes.c_void_p
        kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
        handle = kernel32.OpenProcess(0x1000, False, int(pid))  # QUERY_LIMITED_INFORMATION
        if not handle:
            return False
        try:
            code = ctypes.c_ulong()
            if not kernel32.GetExitCodeProcess(ctypes.c_void_p(handle),
                                               ctypes.byref(code)):
                return False
            return code.value == 259  # STILL_ACTIVE
        finally:
            kernel32.CloseHandle(ctypes.c_void_p(handle))
    try:
        os.kill(int(pid), 0)
    except OSError:
        return False
    return True


# ---------------------------------------------------------------------------
# Windows process-tree containment
# ---------------------------------------------------------------------------
#: JOBOBJECT_EXTENDED_LIMIT_INFORMATION.BasicLimitInformation.LimitFlags
_JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000
_JOB_OBJECT_EXTENDED_LIMIT_INFORMATION = 9


class _IOCounters(ctypes.Structure):
    _fields_ = [(name, ctypes.c_ulonglong) for name in
                ("ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
                 "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]


class _BasicLimitInformation(ctypes.Structure):
    _fields_ = [("PerProcessUserTimeLimit", ctypes.c_int64),
                ("PerJobUserTimeLimit", ctypes.c_int64),
                ("LimitFlags", ctypes.c_uint32),
                ("MinimumWorkingSetSize", ctypes.c_size_t),
                ("MaximumWorkingSetSize", ctypes.c_size_t),
                ("ActiveProcessLimit", ctypes.c_uint32),
                ("Affinity", ctypes.c_size_t),
                ("PriorityClass", ctypes.c_uint32),
                ("SchedulingClass", ctypes.c_uint32)]


class _ExtendedLimitInformation(ctypes.Structure):
    _fields_ = [("BasicLimitInformation", _BasicLimitInformation),
                ("IoInfo", _IOCounters),
                ("ProcessMemoryLimit", ctypes.c_size_t),
                ("JobMemoryLimit", ctypes.c_size_t),
                ("PeakProcessMemoryUsed", ctypes.c_size_t),
                ("PeakJobMemoryUsed", ctypes.c_size_t)]


def _kernel32():
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateJobObjectW.restype = ctypes.c_void_p
    kernel32.CreateJobObjectW.argtypes = [ctypes.c_void_p, ctypes.c_wchar_p]
    kernel32.SetInformationJobObject.argtypes = [ctypes.c_void_p, ctypes.c_int,
                                                 ctypes.c_void_p, ctypes.c_uint32]
    kernel32.AssignProcessToJobObject.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    kernel32.AssignProcessToJobObject.restype = ctypes.c_int
    kernel32.TerminateJobObject.argtypes = [ctypes.c_void_p, ctypes.c_uint]
    kernel32.TerminateJobObject.restype = ctypes.c_int
    kernel32.CloseHandle.argtypes = [ctypes.c_void_p]
    kernel32.CloseHandle.restype = ctypes.c_int
    return kernel32


class _JobTree:
    """Kill-on-close Windows job holding the child and everything it spawns.

    ``taskkill /T`` is not enough on its own: it needs rights over the whole tree
    and it is enumerated by parent pid at kill time, so it is exactly the wrong
    tool here (measured: ``ERROR: Access denied`` while a grandchild survived).
    A job object assigned right after the child starts is inherited by every
    descendant, and ``TerminateJobObject`` then kills the tree in one call with our
    own handle -- no rights over other processes required.  Closing the handle
    kills anything still left, so the deadline also covers cleanup after a normal
    exit.
    """

    def __init__(self, process):
        self._handle = None
        if sys.platform != "win32":
            return
        self._kernel32 = _kernel32()
        handle = self._kernel32.CreateJobObjectW(None, None)
        if not handle:
            raise OSError(ctypes.get_last_error(), "CreateJobObjectW failed")
        info = _ExtendedLimitInformation()
        info.BasicLimitInformation.LimitFlags = _JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
        if not self._kernel32.SetInformationJobObject(
                ctypes.c_void_p(handle), _JOB_OBJECT_EXTENDED_LIMIT_INFORMATION,
                ctypes.byref(info), ctypes.sizeof(info)):
            error = ctypes.get_last_error()
            self._kernel32.CloseHandle(ctypes.c_void_p(handle))
            raise OSError(error, "SetInformationJobObject failed")
        if not self._kernel32.AssignProcessToJobObject(
                ctypes.c_void_p(handle), ctypes.c_void_p(int(process._handle))):
            error = ctypes.get_last_error()
            self._kernel32.CloseHandle(ctypes.c_void_p(handle))
            raise OSError(error, "AssignProcessToJobObject failed")
        self._handle = handle

    def terminate(self, exit_code=1):
        if self._handle is not None:
            self._kernel32.TerminateJobObject(ctypes.c_void_p(self._handle),
                                              int(exit_code))

    def close(self):
        if self._handle is not None:
            self._kernel32.CloseHandle(ctypes.c_void_p(self._handle))
            self._handle = None


def _kill_tree(process, tree=None):
    """Kill the child and everything it started, within ``KILL_GRACE_SECONDS``."""
    if tree is not None:
        tree.terminate(TIMEOUT_EXIT)
    if sys.platform == "win32":
        try:
            subprocess.run(["taskkill", "/PID", str(process.pid), "/T", "/F"],
                           stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                           timeout=KILL_GRACE_SECONDS)
        except (OSError, subprocess.TimeoutExpired):
            pass
    else:
        try:
            os.killpg(os.getpgid(process.pid), signal.SIGKILL)
        except (OSError, ProcessLookupError):
            pass
    try:
        process.kill()
    except OSError:
        pass


def _supervise(argv, total_seconds, keep_logs_env="E1_KEEP_SUPERVISOR_LOGS"):
    """Run ``argv`` under one total deadline; return (exit_code, seconds, out, err).

    The child's stdout/stderr are *files*.  That is the point: a grandchild that
    inherits an open pipe can outlive the direct child forever, which is how the
    round-1 replay turned a 150 s budget into 595.7 s of waiting for EOF.  Files
    cannot be blocked that way, so the deadline below is a real bound on the whole
    call -- kill, reap and grace included.
    """
    holder = Path(tempfile.mkdtemp(prefix="e1_supervise_"))
    out_path, err_path = holder / "child.stdout.txt", holder / "child.stderr.txt"
    started = time.monotonic()
    timed_out = False
    with open(out_path, "wb") as out_stream, open(err_path, "wb") as err_stream:
        flags = 0
        if sys.platform == "win32":
            flags = getattr(subprocess, "CREATE_NEW_PROCESS_GROUP", 0)
        process = subprocess.Popen(
            argv, cwd=str(REPO_ROOT), stdin=subprocess.DEVNULL,
            stdout=out_stream, stderr=err_stream, env=_child_env(),
            creationflags=flags, start_new_session=(sys.platform != "win32"),
        )
        try:
            tree = _JobTree(process)
        except (OSError, AttributeError) as error:
            tree = None  # fall back to taskkill/killpg below
            if sys.platform == "win32":
                # Containment is degraded: say so instead of claiming a tree kill
                # that only taskkill can perform.
                print(f"WARNING: no kill-on-close job for the supervised child "
                      f"({type(error).__name__}: {error}); the timeout falls back to "
                      f"taskkill /T", file=sys.stderr, flush=True)
        try:
            code = process.wait(timeout=total_seconds)
        except subprocess.TimeoutExpired:
            timed_out = True
            _kill_tree(process, tree)
            try:
                code = process.wait(timeout=KILL_GRACE_SECONDS)
            except subprocess.TimeoutExpired:  # pragma: no cover - unkillable child
                code = TIMEOUT_EXIT
        finally:
            if tree is not None:
                tree.close()
    elapsed = time.monotonic() - started
    stdout = out_path.read_bytes().decode("utf-8", "replace")
    stderr = err_path.read_bytes().decode("utf-8", "replace")
    if not os.environ.get(keep_logs_env):
        shutil.rmtree(holder, ignore_errors=True)
    return (TIMEOUT_EXIT if timed_out else code), elapsed, stdout, stderr, timed_out, holder


def _relay_stream(stream, text):
    """Relay captured bytes unchanged (no second round of newline translation)."""
    buffer = getattr(stream, "buffer", None)
    if buffer is not None:
        buffer.write(text.encode("utf-8", "replace"))
        buffer.flush()
    else:
        stream.write(text)
        stream.flush()


def _relay(result, label, total_seconds):
    """Print the supervised run's own output and its real exit status."""
    code, elapsed, stdout, stderr, timed_out, _holder = result
    _relay_stream(sys.stdout, stdout)
    _relay_stream(sys.stderr, stderr)
    if timed_out:
        print(f"INCOMPLETE: {label} did not finish inside its {total_seconds:.0f}s "
              f"total deadline (including process cleanup); exit {TIMEOUT_EXIT}",
              file=sys.stderr, flush=True)
    else:
        print(f"{label} exited {code} after {elapsed:.1f}s "
              f"(total deadline {total_seconds:.0f}s, cleanup included)",
              flush=True)
    return code


# ---------------------------------------------------------------------------
# self-test: the deadline must also cover the child tree (round-1 regression)
# ---------------------------------------------------------------------------
#: a child that starts a grandchild holding the inherited handles and then hangs
_STUCK_GRANDCHILD = "import time\nprint('grandchild alive', flush=True)\ntime.sleep(600)\n"
_STUCK_CHILD = (
    "import subprocess, sys, time\n"
    "marker = sys.argv[1]\n"
    "grandchild = subprocess.Popen([sys.executable, '-B', '-c', sys.argv[2]])\n"
    "open(marker, 'w').write(str(grandchild.pid))\n"
    "print('child alive', flush=True)\n"
    "time.sleep(600)\n"
)
SELF_TEST_SECONDS = 3.0
SELF_TEST_MARGIN_SECONDS = 15.0


def self_test_timeout():
    """Assert the supervisor returns inside its budget and reaps the tree.

    Nothing here touches the repository: the supervised command is a synthetic
    child that spawns a grandchild and never returns.  The assertions are what the
    round-1 replay was missing -- a real exit status, a wall clock inside the
    deadline, and a dead grandchild afterwards.
    """
    holder = Path(tempfile.mkdtemp(prefix="e1_selftest_"))
    marker = holder / "grandchild.pid"
    argv = [sys.executable, "-B", "-c", _STUCK_CHILD, str(marker), _STUCK_GRANDCHILD]
    result = _supervise(argv, SELF_TEST_SECONDS, keep_logs_env="")
    code, elapsed, stdout, stderr, timed_out, _logs = result
    failures = []
    if code != TIMEOUT_EXIT:
        failures.append(f"expected exit {TIMEOUT_EXIT} for a stuck child, got {code}")
    if not timed_out:
        failures.append("the stuck child was not reported as timed out")
    if elapsed > SELF_TEST_SECONDS + SELF_TEST_MARGIN_SECONDS:
        failures.append(f"the supervisor took {elapsed:.1f}s for a "
                        f"{SELF_TEST_SECONDS:.0f}s deadline: the timeout does not "
                        f"cover cleanup")
    if "child alive" not in stdout:
        failures.append(f"the child's output was lost; got {stdout!r}")
    if "grandchild alive" not in stdout:
        failures.append(f"the grandchild's output was lost; got {stdout!r}")
    grandchild = None
    for _ in range(50):
        try:
            grandchild = int(marker.read_text(encoding="utf-8").strip())
            break
        except (OSError, ValueError):
            time.sleep(0.1)
    if grandchild is None:
        failures.append("the grandchild never wrote its pid; the self-test itself "
                        "did not run")
    else:
        deadline = time.monotonic() + SELF_TEST_MARGIN_SECONDS
        while _pid_alive(grandchild) and time.monotonic() < deadline:
            time.sleep(0.2)
        if _pid_alive(grandchild):
            failures.append(f"the grandchild pid {grandchild} survived the "
                            f"supervisor: the timeout did not clean up the tree")
    shutil.rmtree(holder, ignore_errors=True)
    if failures:
        for failure in failures:
            print(f"FAIL E1.self_test_timeout: {failure}", file=sys.stderr, flush=True)
        return 1
    print(f"PASS E1.self_test_timeout (returned {code} after {elapsed:.1f}s for a "
          f"{SELF_TEST_SECONDS:.0f}s deadline, grandchild {grandchild} reaped)",
          flush=True)
    return 0


# ---------------------------------------------------------------------------
# entries
# ---------------------------------------------------------------------------
def _run_cases(selected):
    """Run the selected cases in this process; return 0 only if all passed."""
    failures = []
    for case_id in selected:
        print(f"=== {case_id}", flush=True)
        try:
            CASES[case_id]()
        except AssertionError as error:
            failures.append(case_id)
            print(f"FAIL {case_id}: {error}", file=sys.stderr, flush=True)
        except Exception:  # noqa: BLE001 - any other error is also a failed case
            failures.append(case_id)
            traceback.print_exc()
            print(f"FAIL {case_id}: case raised", file=sys.stderr, flush=True)
        else:
            print(f"PASS {case_id}", flush=True)
    print(f"{len(selected) - len(failures)}/{len(selected)} case(s) passed", flush=True)
    return 1 if failures else 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    total_seconds = DEFAULT_TOTAL_SECONDS
    in_process = False
    selected = []
    while argv:
        argument = argv.pop(0)
        if argument in ("-h", "--help"):
            print(__doc__)
            return 0
        if argument == "--list":
            print("\n".join(CASE_IDS))
            return 0
        if argument == "--in-process":
            in_process = True
            continue
        if argument == "--self-test-timeout":
            return self_test_timeout()
        if argument == "--total-seconds":
            if not argv:
                print("--total-seconds needs a number", file=sys.stderr)
                return 2
            try:
                total_seconds = float(argv.pop(0))
            except ValueError:
                print("--total-seconds needs a number", file=sys.stderr)
                return 2
            continue
        if argument.startswith("-"):
            print(f"unknown option: {argument}", file=sys.stderr)
            return 2
        selected.append(argument)

    unknown = [case for case in selected if case not in CASES]
    if unknown:
        print(f"unknown case id(s): {', '.join(unknown)}", file=sys.stderr)
        print(f"known case ids: {', '.join(CASE_IDS)}", file=sys.stderr)
        return 2
    selected = selected or list(CASE_IDS)

    if in_process:
        return _run_cases(selected)

    argv = [sys.executable, "-B", str(Path(__file__).resolve()), "--in-process", *selected]
    return _relay(_supervise(argv, total_seconds), "E1 quick replay", total_seconds)


if __name__ == "__main__":
    raise SystemExit(main())
