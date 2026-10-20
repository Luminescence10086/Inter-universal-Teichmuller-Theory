#!/usr/bin/env python3
"""Fixture self-tests for audit/tcb_manifest.py.

Four fixtures, each a complete fake Lean project in a TemporaryDirectory:

  (a) over-pinned  - the verifier globs a whole directory but reads one file,
                     so the other file is discovered as pinned-but-unread.
  (b) under-pinned - the verifier reads a file the pin map never records, so
                     the evidence gap is discovered.
  (c) closure      - the read lives in a sibling module imported at the top of
                     the verifier: the closure must still contain it.
  (d) honest       - the pin equals the read set: no findings, exit code 0.

Two more checks guard the rest of the contract: a dynamically computed path
must be reported as UNRESOLVED and make the tool exit 3 (never a silent
"complete" claim), and --propose must remove only the unread keys.

Run: python -m unittest discover -s audit/tests -p "test_tcb*.py" -v
"""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

HERE = Path(__file__).resolve()
AUDIT = HERE.parents[1]
TOOL = AUDIT / "tcb_manifest.py"
sys.path.insert(0, str(AUDIT))

import tcb_manifest  # noqa: E402

d = textwrap.dedent

DIGEST = d("""\
    import hashlib
    from pathlib import Path


    def digest(path):
        with Path(path).open('rb') as stream:
            return hashlib.file_digest(stream, 'sha256').hexdigest()
    """)


def write(root: Path, rel: str, text: str) -> Path:
    path = root / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


def pin(root: Path, keys: list) -> None:
    payload = {"schema": 2, "input_sha256": {k: "0" * 64 for k in keys}}
    write(root, "verification/checked-inputs.json",
          json.dumps(payload, indent=2))


class FixtureCase(unittest.TestCase):
    def analyze(self, root: Path, name: str = "fix") -> dict:
        return tcb_manifest.analyze_project(root, name)

    def run_cli(self, root: Path, *extra: str):
        return subprocess.run(
            [sys.executable, str(TOOL), "--root", str(root), "--project",
             "root", *extra],
            capture_output=True, text=True, encoding="utf-8",
        )

    # -- (a) over-pinning --------------------------------------------------
    def test_a_globbed_directory_over_pins_unread_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "tools/a.py", "VALUE = 1\n")
            write(root, "tools/b.py", "VALUE = 2\n")   # hashed, never read
            write(root, "tools/verify.py", DIGEST + d("""\
                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    paths = {p for p in (ROOT / 'tools').glob('*.py')}
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in paths}


                def main():
                    inputs = snapshot()
                    source = (ROOT / 'tools/a.py').read_text(encoding='utf-8')
                    if not source or not inputs:
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["tools/a.py", "tools/b.py", "tools/verify.py"])
            report = self.analyze(root)

            over = [o["key"] for o in report["over_pinned"]]
            self.assertEqual(over, ["tools/b.py"], report["over_pinned"])
            self.assertEqual(report["under_pinned"], [])
            self.assertIn("tools/a.py", report["read_paths"])
            self.assertNotIn("tools/b.py", report["read_paths"])
            evidence = " ".join(report["over_pinned"][0]["evidence"])
            self.assertIn("glob('*.py')", evidence)
            self.assertIn("tools/verify.py", evidence)
            self.assertEqual(self.run_cli(root).returncode, 2)

    # -- (b) under-pinning -------------------------------------------------
    def test_b_read_but_unpinned_file_is_detected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "tools/a.py", "VALUE = 1\n")
            write(root, "data/extra.json", '{"secret": 1}\n')
            write(root, "tools/verify.py", DIGEST + d("""\
                import json

                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    paths = [ROOT / 'tools/a.py']
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in paths}


                def main():
                    inputs = snapshot()
                    (ROOT / 'tools/a.py').read_text(encoding='utf-8')
                    config = json.loads(
                        (ROOT / 'data/extra.json').read_text(encoding='utf-8'))
                    if not config or not inputs:
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["tools/a.py", "tools/verify.py"])
            report = self.analyze(root)

            under = [u["key"] for u in report["under_pinned"]]
            self.assertEqual(under, ["data/extra.json"], report["under_pinned"])
            self.assertEqual([o["key"] for o in report["over_pinned"]], [])
            site = report["under_pinned"][0]["sites"][0]
            self.assertEqual(site["kind"], "read_text")
            self.assertIn("data/extra.json", site["snippet"])
            self.assertEqual(self.run_cli(root).returncode, 2)

    # -- (c) sibling-module closure ---------------------------------------
    def test_c_imported_sibling_module_is_in_closure(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "data/sibling.json", '{"k": 2}\n')
            write(root, "tools/helper.py", d("""\
                from pathlib import Path


                def load(root):
                    return (root / 'data/sibling.json').read_text(
                        encoding='utf-8')
                """))
            write(root, "tools/verify.py", DIGEST + d("""\
                from helper import load

                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    paths = [ROOT / p for p in
                             ('data/sibling.json', 'tools/verify.py',
                              'tools/helper.py')]
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in paths}


                def main():
                    inputs = snapshot()
                    if not load(ROOT) or not inputs:
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["data/sibling.json", "tools/helper.py",
                       "tools/verify.py"])
            report = self.analyze(root)

            # closure completeness: the imported module and its read are both
            # in the read set although verify.py never names the data file
            self.assertIn("tools/helper.py", report["modules_analyzed"])
            self.assertIn("data/sibling.json", report["read_paths"])
            self.assertIn("tools/helper.py", report["read_paths"])
            self.assertEqual([o["key"] for o in report["over_pinned"]], [])
            self.assertEqual([u["key"] for u in report["under_pinned"]], [])
            self.assertEqual(self.run_cli(root).returncode, 0)

    # -- (d) honest verifier ----------------------------------------------
    def test_d_honest_verifier_has_no_findings(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "tools/a.py", "VALUE = 1\n")
            write(root, "tools/verify.py", DIGEST + d("""\
                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    paths = [ROOT / 'tools/a.py', ROOT / 'tools/verify.py']
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in paths}


                def main():
                    inputs = snapshot()
                    source = (ROOT / 'tools/a.py').read_text(encoding='utf-8')
                    if not source or not inputs:
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["tools/a.py", "tools/verify.py"])
            report = self.analyze(root)

            self.assertEqual(report["counts"]["over_pinned"], 0)
            self.assertEqual(report["counts"]["under_pinned"], 0)
            self.assertEqual(report["counts"]["unresolved_repo"], 0)
            result = self.run_cli(root)
            self.assertEqual(result.returncode, 0, result.stderr)

    # -- (e) dynamic path must fail loudly --------------------------------
    def test_e_dynamic_path_is_reported_unresolved(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "tools/a.py", "VALUE = 1\n")
            write(root, "verification/receipt.json",
                  '{"evidence": "log.txt"}\n')
            write(root, "verification/log.txt", "observed\n")
            write(root, "tools/verify.py", DIGEST + d("""\
                import json

                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    paths = [ROOT / 'tools/a.py', ROOT / 'tools/verify.py']
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in paths}


                def main():
                    inputs = snapshot()
                    receipt = json.loads(
                        (ROOT / 'verification/receipt.json').read_text(
                            encoding='utf-8'))
                    computed = 'verification/' + receipt['evidence']
                    (ROOT / computed).read_text(encoding='utf-8')
                    if not inputs:
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["tools/a.py", "tools/verify.py"])
            report = self.analyze(root)

            self.assertGreaterEqual(report["counts"]["unresolved_repo"], 1,
                                    report["unresolved"])
            self.assertEqual(self.run_cli(root).returncode, 3)

    # -- proposal ---------------------------------------------------------
    def test_proposal_removes_only_unread_keys(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "tools/a.py", "VALUE = 1\n")
            write(root, "tools/b.py", "VALUE = 2\n")
            write(root, "tools/verify.py", DIGEST + d("""\
                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    paths = [ROOT / 'tools/a.py', ROOT / 'tools/b.py',
                             ROOT / 'tools/verify.py']
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in paths}


                def main():
                    inputs = snapshot()
                    (ROOT / 'tools/a.py').read_text(encoding='utf-8')
                    if not inputs:
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["tools/a.py", "tools/b.py", "tools/verify.py"])
            result = self.run_cli(root, "--propose")
            self.assertIn(result.returncode, (2, 3), result.stderr)
            payload = json.loads(result.stdout)
            proposed = payload["proposed_pin"]
            self.assertIn("tools/a.py", proposed)
            self.assertNotIn("tools/b.py", proposed)
            self.assertEqual([r["key"] for r in payload["removed"]],
                             ["tools/b.py"])
            self.assertTrue(payload["removed"][0]["reason"])
            # the proposal must never be written into the project
            self.assertFalse((root / "proposal.json").exists())
            self.assertFalse((root / "audit").exists())

    # -- CLI surface ------------------------------------------------------
    def test_help_and_json(self):
        result = subprocess.run([sys.executable, str(TOOL), "--help"],
                                capture_output=True, text=True,
                                encoding="utf-8")
        self.assertEqual(result.returncode, 0)
        for flag in ("--project", "--propose", "--json"):
            self.assertIn(flag, result.stdout)

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            write(root, "tools/verify.py", DIGEST + d("""\
                ROOT = Path(__file__).resolve().parents[1]


                def snapshot():
                    return {p.relative_to(ROOT).as_posix(): digest(p)
                            for p in [ROOT / 'tools/verify.py']}


                def main():
                    if not snapshot():
                        raise SystemExit(1)


                if __name__ == '__main__':
                    main()
                """))
            pin(root, ["tools/verify.py"])
            result = self.run_cli(root, "--json")
            payload = json.loads(result.stdout)
            self.assertEqual(len(payload), 1)
            self.assertEqual(payload[0]["project"], "root")
            self.assertEqual(payload[0]["counts"]["pinned"], 1)
            self.assertEqual(payload[0]["counts"]["over_pinned"], 0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
