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
injected as narrowly as possible. All other required probes still run for real.
The untouched baseline runs the full
M1-M8 matrix once; the focused failure cases skip that repeated matrix so each
probe contract can be checked quickly and independently.

Two entry points assert the same things:

    python -B audit/tests/test_mutation_probe_exit.py <CASE_ID>   # exactly one case
    python -B -m unittest discover -s audit/tests -p "test_*.py"  # whole suite

The complete M1-M8 matrix runs once in the baseline case. Focused probe-failure
cases do not repeat it; all required contract probes still run in each case.
Use ``audit/tests/run_mutation_probe_exit_quick.py`` for a 270-second total
timeout whose Windows wrapper kills the complete child process tree.
"""
from __future__ import annotations

import contextlib
import io
import json
import shutil
import sys
import tempfile
import traceback
import unittest
from pathlib import Path

AUDIT = Path(__file__).resolve().parents[1]
if str(AUDIT) not in sys.path:
    sys.path.insert(0, str(AUDIT))
sys.dont_write_bytecode = True

import mutation_harness as mh  # noqa: E402

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
    failing = {name: cell.get("detail") for name, cell in report["probes"].items()
               if cell.get("ok") is not True}
    assert not failing, f"probes must pass on the untouched repository: {failing}"


# ---------------------------------------------------------------------------
# case 2: the reviewer's real counterexample (Kept, not weakened)
# ---------------------------------------------------------------------------
def case_fact_tree_removal_regression():
    """Reproduce the reviewer's counterexample without editing any file.

    ``freshness.validate_project`` is wrapped in memory so that *only* the real
    target-set/admission rejection is swallowed (exactly the bypass used in
    ``reviews/4841271-acceptance/astra/reproduce_mutation_exit.py``).  Both
    baselines and all of M1-M8 still run normally.  Before the fix this run ended
    with ``fact_tree_removal.ok=false``, ``violations=[]`` and ``exit_code=0``.
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

    with _probe_outcomes(unpin_entry=failing):
        code, report, _, stderr = _cli()
    _report(code, report, stderr, "E1.unpin_entry_failure")
    assert report["probes"]["unpin_entry"]["ok"] is False
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
        code, report, _, stderr = _cli()
    finally:
        mh.subprocess = saved
    _report(code, report, stderr, "E1.clean_checkout_failure")
    probe = report["probes"]["clean_checkout_head"]
    assert probe["ok"] is False, probe
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

    with _probe_outcomes(baseline_bridge=failing, baseline_main=failing):
        code, report, _, stderr = _cli()
    _report(code, report, stderr, "E1.baseline_failure")
    for name in ("baseline_bridge", "baseline_main"):
        assert report["probes"][name]["ok"] is False, report["probes"][name]
        _assert_probe_is_named(report, name)
    assert code != 0, (f"a failing baseline was reported as success; "
                       f"violations={report['violations']}")


def case_probe_exception():
    """A probe that raises must become a reported failure, not a pass or a crash."""
    def exploding(tmp=None):
        raise RuntimeError("synthetic probe explosion (E1.probe_exception)")

    with _probe_outcomes(unpin_entry=exploding):
        code, report, _, stderr = _cli()
    _report(code, report, stderr, "E1.probe_exception")
    assert code != 0, ("a probe that raised was reported as success; "
                       f"violations={report['violations']}")
    assert report["exit_code"] != 0
    assert report["probes"]["unpin_entry"]["ok"] is False
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

    with _probe_outcomes(unpin_entry=no_verdict,
                         clean_checkout_head=not_a_mapping):
        code, report, _, stderr = _cli()
    _report(code, report, stderr, "E1.malformed_probe_result")
    assert code != 0, ("malformed probe results were reported as success; "
                       f"violations={report['violations']}")
    assert report["probes"]["unpin_entry"]["ok"] is False
    assert report["probes"]["clean_checkout_head"]["ok"] is False
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
# single-case replay entry (frozen argv)
# ---------------------------------------------------------------------------
def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv and argv[0] in ("-h", "--help"):
        print(__doc__)
        return 0
    if argv and argv[0] == "--list":
        print("\n".join(CASE_IDS))
        return 0
    unknown = [case for case in argv if case not in CASES]
    if unknown:
        print(f"unknown case id(s): {', '.join(unknown)}", file=sys.stderr)
        print(f"known case ids: {', '.join(CASE_IDS)}", file=sys.stderr)
        return 2

    selected = argv or list(CASE_IDS)
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
    print(f"{len(selected) - len(failures)}/{len(selected)} case(s) passed")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
