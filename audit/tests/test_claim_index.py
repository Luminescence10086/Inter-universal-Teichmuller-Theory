#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests for audit/claim_index.py.

Fixtures live in a fresh temporary directory per test.  Nothing here reads or
writes the real repository: each test builds a miniature repo root containing
one fact-tree export and a handful of markdown files, then runs the CLI as a
subprocess exactly as a human would.

Run:  python audit/tests/test_claim_index.py        (or python -m unittest)
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(os.path.dirname(HERE), "claim_index.py")

# Two real-shaped theorem ids; the dangling fixture must not be one of them.
REAL = [
    "IUTBridge.ScaleLedger.cost_exact",
    "IUTAudit.Scale.scale_composition",
]

FACTS = {"schema": 2, "nodes": [{"id": i, "kind": "theorem", "status": "admitted"}
                                for i in REAL]}


class ClaimIndexTest(unittest.TestCase):
    # -- helpers ---------------------------------------------------------
    def make_root(self, docs: dict) -> str:
        root = tempfile.mkdtemp(prefix="claimidx-")
        os.makedirs(os.path.join(root, "fact-tree"), exist_ok=True)
        os.makedirs(os.path.join(root, "research"), exist_ok=True)
        with open(os.path.join(root, "fact-tree", "facts.json"), "w",
                  encoding="utf-8") as fh:
            json.dump(FACTS, fh)
        for name, body in docs.items():
            path = os.path.join(root, name.replace("/", os.sep))
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(body)
        return root

    def run_cli(self, root, *args):
        proc = subprocess.run(
            [sys.executable, SCRIPT, "--root", root, *args],
            capture_output=True, text=True, encoding="utf-8",
        )
        return proc

    def index(self, root, *args):
        proc = self.run_cli(root, "--json", *args)
        self.assertIn(proc.returncode, (0, 1), proc.stderr)
        return json.loads(proc.stdout)

    @staticmethod
    def file_entry(index, path):
        for f in index["files"]:
            if f["path"] == path:
                return f
        raise AssertionError("file not indexed: %s" % path)

    # -- (i) anchored claim passes ---------------------------------------
    def test_anchored_claim_passes(self):
        root = self.make_root({
            "research/anchored.md":
                "The theorem `IUTBridge.ScaleLedger.cost_exact` is verified.\n",
        })
        idx = self.index(root)
        f = self.file_entry(idx, "research/anchored.md")
        self.assertEqual((f["claims"], f["anchored"], f["narrative"],
                          f["unanchored"], f["dangling"]), (1, 1, 0, 0, 0))
        self.assertEqual(idx["totals"]["anchored"], 1)
        self.assertEqual(idx["totals"]["unanchored"], 0)
        self.assertEqual(idx["totals"]["dangling"], 0)
        self.assertEqual(self.run_cli(root).returncode, 0)
        # --strict must not fail either: nothing is unanchored.
        self.assertEqual(self.run_cli(root, "--strict").returncode, 0)

    # -- (ii) stale dotted id is dangling and fails ----------------------
    def test_dangling_anchor_fails(self):
        root = self.make_root({
            "research/dangling.md":
                "The theorem `IUTBridge.ScaleLedger.cost_exact_v2` is proved.\n",
        })
        idx = self.index(root)
        f = self.file_entry(idx, "research/dangling.md")
        self.assertEqual((f["claims"], f["anchored"], f["unanchored"],
                          f["dangling"]), (1, 0, 0, 1))
        self.assertEqual(idx["totals"]["dangling"], 1)
        item = f["items"][0]
        self.assertEqual(item["status"], "dangling")
        self.assertEqual(item["dangling"], ["IUTBridge.ScaleLedger.cost_exact_v2"])
        # dangling is a hard error, with or without --strict.
        self.assertEqual(self.run_cli(root).returncode, 1)
        self.assertEqual(self.run_cli(root, "--strict").returncode, 1)

    # -- (iii) overclaim with no anchor is unanchored --------------------
    def test_unanchored_overclaim_reported_not_fatal(self):
        root = self.make_root({
            "research/overclaim.md":
                "This proves every layer is strictly increasing.\n",
        })
        idx = self.index(root)
        f = self.file_entry(idx, "research/overclaim.md")
        self.assertEqual((f["claims"], f["anchored"], f["narrative"],
                          f["unanchored"]), (1, 0, 0, 1))
        self.assertEqual(idx["totals"]["unanchored"], 1)
        self.assertEqual(idx["totals"]["dangling"], 0)
        # Default: reported, not fatal.  --strict: fatal.
        self.assertEqual(self.run_cli(root).returncode, 0)
        strict = self.run_cli(root, "--strict")
        self.assertEqual(strict.returncode, 1)
        self.assertIn("--strict", strict.stdout)

    # -- (iv) narrative marker is a waiver, not a defect -----------------
    def test_narrative_marker_is_waived(self):
        root = self.make_root({
            "research/waived.md":
                "<!-- narrative --> This narrative sentence proves every layer grows.\n",
        })
        idx = self.index(root)
        f = self.file_entry(idx, "research/waived.md")
        self.assertEqual((f["claims"], f["anchored"], f["narrative"],
                          f["unanchored"]), (1, 0, 1, 0))
        self.assertEqual(idx["totals"]["narrative"], 1)
        self.assertEqual(idx["totals"]["unanchored"], 0)
        self.assertEqual(self.run_cli(root, "--strict").returncode, 0)
        self.assertIn("NARRATIVE", self.run_cli(root).stdout)

    # -- regression: theorem tables must not be silently dropped ---------
    def test_table_rows_count_and_anchor(self):
        root = self.make_root({
            "bridges/index.md":
                "| label | kind | theorem | verdict |\n"
                "|---|---|---|---|\n"
                "| `BR-01` | instantiation | `IUTAudit.Scale.scale_composition` | checked |\n"
                "| `BR-02` | new_result | `cost_exact` | checked |\n",
        })
        idx = self.index(root)
        f = self.file_entry(idx, "bridges/index.md")
        # header row: no backticked ident -> not a claim; separator -> skipped
        self.assertEqual(f["claims"], 2)
        self.assertEqual(f["anchored"], 1)
        self.assertEqual(f["unanchored"], 1)
        self.assertEqual([i["line"] for i in f["items"]], [3, 4])

    # -- --fix-hints maps an abbreviated id to a real one ----------------
    def test_fix_hints_suggests_fully_qualified_id(self):
        root = self.make_root({
            "research/bare.md":
                "The theorem `cost_exact` fixes the layer image.\n",
        })
        proc = self.run_cli(root, "--fix-hints")
        self.assertEqual(proc.returncode, 0)
        self.assertIn("IUTBridge.ScaleLedger.cost_exact", proc.stdout)
        idx = self.index(root)
        hints = self.file_entry(idx, "research/bare.md")["items"][0]["hints"]
        self.assertEqual(hints[0]["closest"], "IUTBridge.ScaleLedger.cost_exact")

    # -- a filename is not a theorem reference ---------------------------
    def test_filenames_are_not_dangling(self):
        root = self.make_root({
            "research/files.md":
                "The verifier `tools/verify.py` produces `facts.json`, per `Export.lean`.\n",
        })
        idx = self.index(root)
        self.assertEqual(idx["totals"]["dangling"], 0)
        self.assertEqual(self.run_cli(root).returncode, 0)

    # -- determinism -----------------------------------------------------
    def test_output_is_deterministic(self):
        root = self.make_root({
            "research/a.md": "The theorem `IUTAudit.Scale.scale_composition` holds.\n",
        })
        self.assertEqual(self.run_cli(root, "--json").stdout,
                         self.run_cli(root, "--json").stdout)

    # -- usage errors ----------------------------------------------------
    def test_missing_fact_tree_is_exit_2(self):
        root = self.make_root({"research/a.md": "Proved, exactly.\n"})
        os.remove(os.path.join(root, "fact-tree", "facts.json"))
        self.assertEqual(self.run_cli(root).returncode, 2)

    def test_help_exits_zero(self):
        proc = subprocess.run([sys.executable, SCRIPT, "--help"],
                              capture_output=True, text=True, encoding="utf-8")
        self.assertEqual(proc.returncode, 0)
        self.assertIn("anchor syntax", proc.stdout)


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    unittest.main(verbosity=2)
