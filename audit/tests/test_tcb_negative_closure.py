#!/usr/bin/env python3
"""E3 negative closure tests for audit/tcb_manifest.py (acceptance R1/P1).

Each case runs the REAL analyser (``tcb_manifest.analyze_project`` and the real
CLI) on a fixture or on the real bridge project, and several cases also run the
fixture's own verifier before/after changing an input, so the claimed decision
input is grounded in an observable exit-code flip rather than in our opinion.

Frozen invocation (one case per process, exit 0 iff its assertion holds):

    python -B audit/tests/test_tcb_negative_closure.py E3.child_process_input

Case ids:
  E3.child_process_input
  E3.qualified_sibling_input
  E3.real_bridge_consumer_bindings
  E3.simple_complete_read_control
  E3.incomplete_closure_blocks_safe_proposal
  E3.separate_input_dependency_runtime_toolchain

Run every case:      python -B audit/tests/test_tcb_negative_closure.py
Via unittest:        python -B -m unittest discover -s audit/tests -p "test_tcb*.py"
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
import tempfile
import textwrap
import traceback
import unittest
from pathlib import Path

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve()
REPO = HERE.parents[2]
AUDIT = REPO / "audit"
TOOL = AUDIT / "tcb_manifest.py"
sys.path.insert(0, str(AUDIT))

import tcb_manifest  # noqa: E402

d = textwrap.dedent

#: the frozen wording of the new "proposal withheld" condition
WITHHELD = "closure incomplete — proposal withheld"

#: components the withdrawn bridge 36->16 proposal wanted to delete although
#: they still participate in semantic / freshness / contract decisions
BRIDGE_CHAIN_COMPONENTS = (
    "@workspace/tools/freshness.py",
    "@workspace/tools/semantic_lock.py",
    "@workspace/tools/bridge.py",
    "tools/DefinitionBodies.lean",
)

CASES: dict = {}


def case(case_id: str):
    def register(fn):
        CASES[case_id] = fn
        return fn
    return register


# --------------------------------------------------------------------------
# fixture helpers
# --------------------------------------------------------------------------

def write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def pin(root: Path, keys) -> None:
    """Write a real pin map (real sha256), like a verifier would."""
    payload = {"schema": 2, "input_sha256": {
        key: hashlib.sha256((root / key).read_bytes()).hexdigest()
        for key in keys}}
    write(root, "verification/checked-inputs.json",
          json.dumps(payload, indent=2))


def analyze(root: Path, name: str = "root") -> dict:
    return tcb_manifest.analyze_project(root, name)


def run_cli(root: Path, *extra: str):
    return subprocess.run(
        [sys.executable, "-B", str(TOOL), "--root", str(root),
         "--project", "root", *extra],
        capture_output=True, text=True, encoding="utf-8", cwd=str(REPO))


def run_verifier(root: Path):
    return subprocess.run([sys.executable, "-B", "tools/verify.py"],
                          capture_output=True, text=True, encoding="utf-8",
                          cwd=str(root))


def keys_of(entries) -> list:
    return [entry["key"] for entry in entries]


def boundary_kinds(report: dict) -> list:
    return [b["kind"] for b in report["closure"]["boundaries"]]

DIGEST = d("""\
    import hashlib
    from pathlib import Path


    def digest(path):
        with Path(path).open('rb') as stream:
            return hashlib.file_digest(stream, 'sha256').hexdigest()
    """)


# --------------------------------------------------------------------------
# E3.child_process_input
# --------------------------------------------------------------------------

@case("E3.child_process_input")
def child_process_input() -> None:
    """A verifier subprocess reads decision.txt: the pin must be retained.

    The analyser cannot traverse the executed program's own read set, so the
    closure is INCOMPLETE and no removal may be suggested for decision.txt.
    """
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        write(root, "tools/verify.py", d("""\
            import subprocess
            import sys
            from pathlib import Path

            ROOT = Path(__file__).resolve().parents[1]


            def digest(path):
                import hashlib
                with Path(path).open('rb') as stream:
                    return hashlib.file_digest(stream, 'sha256').hexdigest()


            def snapshot():
                paths = [ROOT / p for p in
                         ('decision.txt', 'tools/verify.py', 'tools/child.py')]
                return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}


            def main():
                inputs = snapshot()
                subprocess.run([sys.executable, 'tools/child.py'], check=True)
                if not inputs:
                    raise SystemExit(1)


            if __name__ == '__main__':
                main()
            """))
        write(root, "tools/child.py", d("""\
            from pathlib import Path

            assert Path('decision.txt').read_text(encoding='utf-8').strip() == 'accept'
            """))
        write(root, "decision.txt", "accept\n")
        pin(root, ["decision.txt", "tools/child.py", "tools/verify.py"])

        # Ground truth: this pin is a real decision input, not decoration.
        before = run_verifier(root)
        assert before.returncode == 0, (
            f"fixture verifier should pass, got {before.returncode}: "
            f"{before.stdout}{before.stderr}")
        write(root, "decision.txt", "reject\n")
        after = run_verifier(root)
        assert after.returncode == 1, (
            f"changing decision.txt must flip the verifier exit to 1, got "
            f"{after.returncode}: {after.stdout}{after.stderr}")
        write(root, "decision.txt", "accept\n")

        report = analyze(root)
        closure = report["closure"]
        assert not closure["complete"], "subprocess boundary must make the closure incomplete"
        assert "executed-program" in boundary_kinds(report), boundary_kinds(report)
        assert any("child.py" in b["detail"] for b in closure["boundaries"]), (
            "the boundary must name the executed program", closure["boundaries"])
        assert "decision.txt" in keys_of(report["unclassified"]), (
            "an unvisited pinned input must be unclassified", report["unclassified"])
        assert "decision.txt" not in keys_of(report["over_pinned"]), (
            "an unvisited pinned input must never be called over-pinned")
        proposal = report["proposal"]
        assert proposal["status"] == "WITHHELD", proposal.get("status")
        assert proposal["withheld_reason"] == WITHHELD, proposal.get("withheld_reason")
        assert proposal["removed"] == [], proposal["removed"]
        assert "decision.txt" in proposal["proposed_pin"], (
            "the existing pin must be kept", sorted(proposal["proposed_pin"]))
        cli = run_cli(root)
        assert cli.returncode == 4, (
            f"incomplete closure must not exit 0/2, got {cli.returncode}: "
            f"{cli.stdout}{cli.stderr}")


# --------------------------------------------------------------------------
# E3.qualified_sibling_input
# --------------------------------------------------------------------------

@case("E3.qualified_sibling_input")
def qualified_sibling_input() -> None:
    """`import helper; helper.check(ROOT)` reads an unpinned file.

    Either the analyser follows the ordinary module method call (then the
    missing pin must be reported) or it must declare the closure incomplete.
    It must never exit 0 with the input missed.
    """
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        write(root, "tools/verify.py", d("""\
            from pathlib import Path

            import helper

            ROOT = Path(__file__).resolve().parents[1]


            def main():
                helper.check(ROOT)


            if __name__ == '__main__':
                main()
            """))
        write(root, "tools/helper.py", d("""\
            def check(root):
                assert (root / 'decision.txt').read_text(
                    encoding='utf-8').strip() == 'accept'
            """))
        write(root, "decision.txt", "accept\n")
        pin(root, ["tools/helper.py", "tools/verify.py"])   # decision.txt NOT pinned

        before = run_verifier(root)
        assert before.returncode == 0, f"{before.returncode}: {before.stderr}"
        write(root, "decision.txt", "reject\n")
        after = run_verifier(root)
        assert after.returncode == 1, (
            f"changing decision.txt must flip the verifier exit to 1, got "
            f"{after.returncode}: {after.stderr}")
        write(root, "decision.txt", "accept\n")

        report = analyze(root)
        followed = "tools/helper.py" in report["modules_analyzed"]
        assert followed, (
            "the sibling module must be analysed", report["modules_analyzed"])
        under = keys_of(report["under_pinned"])
        complete = report["closure"]["complete"]
        assert "decision.txt" in under or not complete, (
            "a missed decision input must be reported as missing pin or as an "
            f"incomplete closure; under={under} complete={complete}")
        if complete:
            assert "decision.txt" in under, (under, report["under_pinned"])
            assert "decision.txt" in report["proposal"]["added"], (
                "the proposal must ask for the missing pin",
                report["proposal"]["added"])
        cli = run_cli(root, "--json")
        assert cli.returncode != 0, (
            f"CLI must not report success with the input missed (exit "
            f"{cli.returncode}): {cli.stdout}")
        payload = json.loads(cli.stdout)
        assert payload[0]["counts"]["under_pinned"] >= 1 or not payload[0]["closure"]["complete"], (
            "CLI JSON must not claim a clean, complete closure", payload[0]["counts"])


# --------------------------------------------------------------------------
# E3.real_bridge_consumer_bindings
# --------------------------------------------------------------------------

@case("E3.real_bridge_consumer_bindings")
def real_bridge_consumer_bindings() -> None:
    """The real bridge: no component still used by the evidence chain may be
    proposed for removal. Without a closed dependency certificate the existing
    36-key rule is kept."""
    bridge = REPO / "bridge"
    report = tcb_manifest.analyze_project(bridge, "bridge")
    proposal = report["proposal"]
    pinned = sorted(report["proposal"]["proposed_pin"])
    removed = keys_of(proposal["removed"])

    assert report["counts"]["pinned"] == 36, (
        f"frozen 36-key bridge rule changed: {report['counts']['pinned']}")
    assert proposal["status"] == "WITHHELD", proposal.get("status")
    assert proposal["withheld_reason"] == WITHHELD
    assert proposal["removed"] == [], removed
    assert len(pinned) == 36, (len(pinned), pinned)
    for key in BRIDGE_CHAIN_COMPONENTS:
        assert key in pinned, f"{key} was dropped from the kept pin"
        assert key not in removed, f"{key} must not be proposed for removal"

    closure = report["closure"]
    assert not closure["complete"], "the real bridge closure must be declared incomplete"
    details = " ".join(b["detail"] + " " + b["file"] for b in closure["boundaries"])
    for needle in ("semantic_lock.py", "freshness.py"):
        assert needle in details, (
            f"{needle} must be declared an unanalysed consumer, not ignored",
            closure["boundaries"])
    assert "lean-build" in boundary_kinds(report), (
        "Lean build/import consumption must be a declared boundary",
        boundary_kinds(report))
    assert keys_of(report["over_pinned"]) == [], report["over_pinned"]

    cli = run_cli(bridge, "--propose")
    assert cli.returncode == 4, (
        f"incomplete bridge closure must exit 4, got {cli.returncode}: {cli.stderr}")
    payload = json.loads(cli.stdout)
    assert payload["status"] == "WITHHELD", payload["status"]
    assert payload["removed"] == [], payload["removed"]
    assert payload["withheld_reason"] == WITHHELD


# --------------------------------------------------------------------------
# E3.simple_complete_read_control
# --------------------------------------------------------------------------

@case("E3.simple_complete_read_control")
def simple_complete_read_control() -> None:
    """A plain direct-read verifier must still get a definite, complete verdict
    (the conservative fix must not degenerate into 'everything UNRESOLVED')."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        write(root, "config/settings.json", '{"mode": "strict"}\n')
        write(root, "tools/verify.py", DIGEST + d("""\
            import json

            ROOT = Path(__file__).resolve().parents[1]


            def load_config():
                return json.loads(
                    (ROOT / 'config/settings.json').read_text(encoding='utf-8'))


            def snapshot():
                paths = [ROOT / 'config/settings.json', ROOT / 'tools/verify.py']
                return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}


            def main():
                inputs = snapshot()
                config = load_config()
                if not config or not inputs:
                    raise SystemExit(1)


            if __name__ == '__main__':
                main()
            """))
        pin(root, ["config/settings.json", "tools/verify.py"])

        assert run_verifier(root).returncode == 0
        report = analyze(root)
        closure = report["closure"]
        assert closure["complete"], (
            "a plain direct-read verifier must have a complete closure",
            closure["boundaries"])
        assert closure["boundaries"] == [], closure["boundaries"]
        assert report["read_paths"] == ["config/settings.json", "tools/verify.py"], (
            report["read_paths"])
        assert report["counts"]["unresolved_repo"] == 0, report["unresolved"]
        assert keys_of(report["over_pinned"]) == [], report["over_pinned"]
        assert keys_of(report["under_pinned"]) == [], report["under_pinned"]
        proposal = report["proposal"]
        assert proposal["status"] == "PROPOSED", proposal["status"]
        assert proposal["withheld"] is False
        assert sorted(proposal["proposed_pin"]) == [
            "config/settings.json", "tools/verify.py"], proposal["proposed_pin"]
        assert proposal["removed"] == []
        cli = run_cli(root)
        assert cli.returncode == 0, (
            f"a complete clean fixture must still exit 0, got {cli.returncode}: "
            f"{cli.stdout}{cli.stderr}")


# --------------------------------------------------------------------------
# E3.incomplete_closure_blocks_safe_proposal
# --------------------------------------------------------------------------

INCOMPLETE_VERIFY = d("""\
    import subprocess
    import sys
    from pathlib import Path

    ROOT = Path(__file__).resolve().parents[1]


    def digest(path):
        import hashlib
        with Path(path).open('rb') as stream:
            return hashlib.file_digest(stream, 'sha256').hexdigest()


    def snapshot():
        paths = {p for p in (ROOT / 'tools').glob('*.py')}
        return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}


    def main():
        inputs = snapshot()
        subprocess.run([sys.executable, 'tools/child.py'], check=True)
        if not inputs:
            raise SystemExit(1)


    if __name__ == '__main__':
        main()
    """)

COMPLETE_VERIFY = INCOMPLETE_VERIFY.replace(
    "    subprocess.run([sys.executable, 'tools/child.py'], check=True)\n", "")


def _build_gate_fixture(root: Path, verifier_source: str) -> None:
    write(root, "tools/verify.py", verifier_source)
    write(root, "tools/a.py", "VALUE = 1\n")
    write(root, "tools/spare.py", "VALUE = 2\n")     # hashed, never interpreted
    write(root, "tools/child.py", "from pathlib import Path\n"
                                  "assert Path('decision.txt').read_text("
                                  "encoding='utf-8').strip() == 'accept'\n")
    write(root, "decision.txt", "accept\n")
    pin(root, ["decision.txt", "tools/a.py", "tools/child.py", "tools/spare.py",
               "tools/verify.py"])


@case("E3.incomplete_closure_blocks_safe_proposal")
def incomplete_closure_blocks_safe_proposal() -> None:
    """While the closure is incomplete no safe-to-remove pin proposal exists;
    the same fixture with a complete closure still yields a removal."""
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        _build_gate_fixture(root, INCOMPLETE_VERIFY)
        assert run_verifier(root).returncode == 0
        report = analyze(root)
        closure = report["closure"]
        assert not closure["complete"], closure["boundaries"]
        assert "tools/spare.py" in keys_of(report["unclassified"]), (
            "the unread pin must be unclassified, not declared useless",
            report["unclassified"])
        assert report["counts"]["over_pinned"] == 0, report["over_pinned"]
        proposal = report["proposal"]
        assert proposal["status"] == "WITHHELD"
        assert proposal["withheld_reason"] == WITHHELD, proposal["withheld_reason"]
        assert proposal["removed"] == [], proposal["removed"]
        assert sorted(proposal["proposed_pin"]) == [
            "decision.txt", "tools/a.py", "tools/child.py", "tools/spare.py",
            "tools/verify.py"], sorted(proposal["proposed_pin"])
        cli = run_cli(root, "--propose")
        assert cli.returncode == 4, (cli.returncode, cli.stdout, cli.stderr)
        payload = json.loads(cli.stdout)
        assert payload["status"] == "WITHHELD" and payload["removed"] == []
        assert payload["withheld_reason"] == WITHHELD

        # Control: drop the subprocess boundary and the SAME fixture is allowed
        # to propose removing the unread pin.  The gate is not "always refuse".
        write(root, "tools/verify.py", COMPLETE_VERIFY)
        control = analyze(root)
        assert control["closure"]["complete"], control["closure"]["boundaries"]
        assert "tools/spare.py" in keys_of(control["over_pinned"]), (
            control["over_pinned"])
        ctl = control["proposal"]
        assert ctl["status"] == "PROPOSED", ctl["status"]
        assert ctl["withheld"] is False and ctl["withheld_reason"] is None
        assert "tools/spare.py" in keys_of(ctl["removed"]), ctl["removed"]
        assert run_cli(root, "--propose").returncode == 2


# --------------------------------------------------------------------------
# E3.separate_input_dependency_runtime_toolchain
# --------------------------------------------------------------------------

@case("E3.separate_input_dependency_runtime_toolchain")
def separate_input_dependency_runtime_toolchain() -> None:
    """input / dependency / runtime / toolchain are reported separately, and a
    Lean source consumed by the toolchain is not called a Python-hash-only
    artefact."""
    bridge = REPO / "bridge"
    report = tcb_manifest.analyze_project(bridge, "bridge")
    cats = report["categories"]
    assert set(cats) == {"input", "dependency", "runtime", "toolchain"}, sorted(cats)
    assert cats["input"]["pinned"] == 36, cats["input"]

    dep = report["dependency_map"]
    toolchain_keys = [e["key"] for e in dep["toolchain_consumed"]]
    unclassified_dep = [e["key"] for e in dep["unclassified"]]
    assert toolchain_keys, "the Lean dependency sources must be reported"
    lean_config = {"lean-toolchain", "lakefile.toml", "lake-manifest.json"}
    for key in toolchain_keys:
        base = key.replace("\\", "/").rsplit("/", 1)[-1]
        assert base.endswith(".lean") or base in lean_config, key
        assert key not in unclassified_dep, f"{key} classified twice"
        assert key not in keys_of(report["proposal"]["removed"]), (
            f"{key} must not be proposed for removal")
        entry = next(e for e in dep["toolchain_consumed"] if e["key"] == key)
        assert entry["category"] == "toolchain", entry
        # the withdrawn claim: "only Python hashes it"
        assert "Lean import/build graph" in entry["reason"], entry["reason"]
        assert "not evidence" in entry["reason"], entry["reason"]
        assert "verifier only interprets" not in entry["reason"], entry["reason"]
    assert cats["dependency"]["toolchain_consumed"] == len(toolchain_keys)
    assert cats["toolchain"]["dependency_lean_sources"] == toolchain_keys
    assert cats["toolchain"]["lean_build_boundaries"] >= 1, cats["toolchain"]
    assert "lake" in cats["runtime"]["external_tools"], cats["runtime"]
    assert cats["input"]["consumed"] + cats["input"]["unclassified"] \
        + cats["input"]["declared_platform_inputs"] == 36, cats["input"]
    # categories must not swallow each other
    assert dep["over"] == [], dep["over"]
    assert report["counts"]["over_pinned"] == 0, report["over_pinned"]


# --------------------------------------------------------------------------
# unittest surface + frozen single-case CLI
# --------------------------------------------------------------------------

class NegativeClosureCases(unittest.TestCase):
    """One test method per required case id."""


def _install(case_id: str, fn) -> None:
    name = "test_" + re.sub(r"[^0-9a-z]+", "_", case_id.lower())
    setattr(NegativeClosureCases, name, lambda self, _fn=fn: _fn())


for _cid, _fn in sorted(CASES.items()):
    _install(_cid, _fn)


def main(argv=None) -> int:
    args = list(sys.argv[1:] if argv is None else argv)
    if args and args[0] in ("-l", "--list"):
        print("\n".join(sorted(CASES)))
        return 0
    if not args:
        loader = unittest.TestLoader()
        suite = loader.loadTestsFromTestCase(NegativeClosureCases)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1
    case_id = args[0]
    if case_id not in CASES:
        print(f"UNKNOWN CASE {case_id!r}; known: {', '.join(sorted(CASES))}")
        return 2
    try:
        CASES[case_id]()
    except AssertionError:
        print(f"RESULT {case_id} FAIL")
        traceback.print_exc()
        return 1
    except Exception:                      # a crashing case is not a pass
        print(f"RESULT {case_id} FAIL")
        traceback.print_exc()
        return 1
    print(f"RESULT {case_id} PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
