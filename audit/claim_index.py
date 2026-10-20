#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""claim_index.py -- claim -> theorem traceability index for the IUT audit repo.

Borrows three ideas:

  * doctest / literate testing: prose is not trusted, executable references are.
    Here the "executable" check is that a claim names a theorem id that the
    fact-tree export actually contains.
  * SBOM provenance: every assertion about the artifact must carry a component
    pointer into a manifest that was produced by the build, not by the author.
  * explicit waivers: unanchored claims are allowed only when declared, and
    declared ones (narrative) are listed rather than silently ignored.

This program is a READ-ONLY indexer.  It never edits the markdown it reads.

Anchor syntax (the convention this tool enforces and documents)
--------------------------------------------------------------
A claim is *anchored* when, inside the same sentence or the same markdown
table row, it contains the fully-qualified id of a theorem that exists in one
of the fact-tree exports, e.g.

    The cost identity is `IUTBridge.ScaleLedger.cost_exact` .

The id may be inside backticks or plain; both are accepted, but the id must be
*fully qualified* (every dotted segment, namespace included).  An abbreviated
reference such as `cost_exact` is NOT an anchor, even if it is unambiguous --
the point of the index is that a reader (and a machine) can resolve it without
guessing.  `--fix-hints` turns such abbreviations into the FQ id.

A claim may instead be *narrative*: an explicit waiver, meaning "this sentence
is commentary and makes no machine fact".  Write either the HTML marker

    <!-- narrative -->

or the bare word `narrative` somewhere in that line.  Narrative claims are
listed, never failed.

Two failure classes
-------------------
* unanchored (the defect class this tool exists for): a machine-fact claim with
  no anchor and no waiver, e.g. "the layer ladder is strictly increasing" when
  the theorem is antitone.
* dangling (hard error): an anchor-shaped reference -- a repo namespace with
  at least namespace.module.decl segments -- that no fact-tree contains.  That
  is a stale reference: the doc cites a theorem that the build does not have.

Exit status
-----------
0  no dangling anchor (and, with --strict, no unanchored claim either)
1  dangling anchor present, or (--strict) unanchored claims present
2  usage / IO problem (e.g. no fact-tree found)

Keep this file stdlib-only and deterministic: no clocks, no network, sorted
iteration everywhere, UTF-8 output.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import sys

# --------------------------------------------------------------------------
# Configuration
# --------------------------------------------------------------------------

#: Fact-tree exports, relative to the repo root.  These are the *only* sources
#: of truth; the index never reads .lean files, so an id that is in the source
#: tree but not in the export is (correctly) reported as dangling.
FACT_TREES = (
    "fact-tree/facts.json",
    "local-field/fact-tree/facts.json",
    "bridge/fact-tree/facts.json",
)

#: Documentation that makes machine-fact claims, relative to the repo root.
DOC_GLOBS = (
    "research/*.md",
    "bridge/README.md",
    "README.md",
    "GAP*.md",
    "bridges/index.md",
)

#: Sentence triggers: a sentence containing one of these is a claim about the
#: machine (a theorem, a proof, an admission, a verification).
TRIGGER_RE = re.compile(
    r"\btheorem"          # theorem, theorems, theorem's
    r"|\bLean\b"
    r"|\bprov(?:ed|es|en|ing)\b"
    r"|\bverified\b"
    r"|\bformaliz(?:ed|able|es)\b"   # "cannot be formalized" is a machine fact
    r"|准入|已验收|已证|定理|引理|形式化",
    re.UNICODE,
)

#: Quantitative triggers: a sentence that quantifies ("only", "every", "恰")
#: asserts something checkable even without naming a theorem.
#:
#: The plain list is exactly the one in the task brief.  `strictly` / `严格`
#: are a deliberate extension: "the ladder is strictly increasing" is the
#: canonical overclaim (the theorem is antitone) and carries none of the
#: brief's words, so without this it would slip through.
QUANT_RE = re.compile(
    r"\bexactly\b|\bonly\b|\bforall\b|\ball\b|\bevery\b|\biff\b|\bstrictly\b"
    r"|对一切|恰|仅|必然|⟺|严格",
    re.UNICODE,
)

#: Waiver markers.
NARRATIVE_MARKER = "<!-- narrative -->"
NARRATIVE_WORD_RE = re.compile(r"\bnarratives?\b", re.IGNORECASE)

#: A dotted identifier: at least one dot, no whitespace, segments are Lean-ish.
DOTTED_RE = re.compile(r"(?<![\w.])([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+)(?![\w.])")
#: A bare identifier (single segment), used by --fix-hints.
BARE_RE = re.compile(r"(?<![\w.])([A-Za-z_][A-Za-z0-9_]*)(?![\w.])")
#: Looser identifier shape, for the *left cell* of a table: contract labels
#: such as `BR-01` or `S6` are identifiers too.
LOOSE_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_.\-]*")
#: Backticked span.
TICKED_RE = re.compile(r"`([^`\n]+)`")

#: File extensions that make a dotted token a filename, not a theorem id.
FILE_EXTS = frozenset(
    {"py", "lean", "md", "json", "toml", "olean", "ilean", "trace", "sh",
     "txt", "csv", "dot", "yaml", "yml", "log", "exe", "lock"}
)

#: Root namespaces of this repo.  A token under one of these with >= 3
#: segments is an *anchor attempt*; module-only (2-segment) mentions such as
#: `IUTAudit.Scale` are treated as prose, not as anchors.
KNOWN_ROOTS = ("IUTAudit", "IUTBridge", "LocalFieldAudit")
MIN_ANCHOR_DEPTH = 3

#: Claim text is truncated for display; JSON keeps its own (longer) limit so
#: that --json stays machine-checkable while the summary stays readable.
SNIPPET = 120
SNIPPET_JSON = 400


# --------------------------------------------------------------------------
# Fact-tree loading
# --------------------------------------------------------------------------

def load_fact_trees(root: str):
    """Return (ids, per-file counts, missing) from the fact-tree exports."""
    ids = {}
    missing = []
    for rel in FACT_TREES:
        path = os.path.join(root, rel.replace("/", os.sep))
        if not os.path.isfile(path):
            missing.append(rel)
            continue
        with open(path, encoding="utf-8") as fh:
            data = json.load(fh)
        nodes = data.get("nodes") or []
        for node in nodes:
            nid = node.get("id")
            if isinstance(nid, str) and nid:
                ids.setdefault(nid, rel)
    return ids, missing


# --------------------------------------------------------------------------
# Claim extraction
# --------------------------------------------------------------------------

def split_sentences(line: str):
    """Split one markdown line into sentences.

    Dots inside backticked spans and dots inside dotted identifiers must not
    split; a dot only ends a sentence when whitespace or end-of-line follows.
    """
    out, buf, in_tick = [], [], False
    n = len(line)
    for i, ch in enumerate(line):
        buf.append(ch)
        if ch == "`":
            in_tick = not in_tick
            continue
        if in_tick:
            continue
        if ch in ".!?;。！？；":
            nxt = line[i + 1] if i + 1 < n else ""
            if nxt == "" or nxt.isspace():
                out.append("".join(buf))
                buf = []
    if buf:
        out.append("".join(buf))
    return [s.strip() for s in out if s.strip()]


def table_cells(line: str):
    """Split a markdown table row into cells (without the outer pipes)."""
    body = line.strip()
    if not body.startswith("|"):
        return None
    if not body.endswith("|"):
        body += "|"
    cells = [c.strip() for c in body[1:-1].split("|")]
    return cells


def is_separator_row(cells) -> bool:
    return all(c == "" or re.fullmatch(r":?-{2,}:?", c) for c in cells)


def has_ticked_ident(cell: str, loose: bool = False) -> bool:
    """True when the cell contains a backticked identifier.

    ``loose`` accepts table-label shapes too (``BR-01``), which is what the
    left cell of a contract table looks like.
    """
    for span in TICKED_RE.findall(cell):
        span = span.strip()
        if DOTTED_RE.fullmatch(span):
            if span.rsplit(".", 1)[-1].lower() not in FILE_EXTS:
                return True
        elif BARE_RE.fullmatch(span):
            return True
        elif loose and LOOSE_IDENT_RE.fullmatch(span):
            return True
    return False


def is_narrative_line(line: str) -> bool:
    if NARRATIVE_MARKER.lower() in line.lower():
        return True
    return bool(NARRATIVE_WORD_RE.search(line))


def looks_like_claim(text: str) -> bool:
    return bool(TRIGGER_RE.search(text) or QUANT_RE.search(text))


def classify_tokens(text: str, known_ids):
    """Return (anchor_ids, dangling_tokens) found in one claim's text."""
    anchors, dangling = [], []
    for tok in set(DOTTED_RE.findall(text)):
        if tok in known_ids:
            anchors.append(tok)
            continue
        last = tok.rsplit(".", 1)[-1]
        if last.lower() in FILE_EXTS:
            continue                      # `verify.py`, `GAP.md`, ...
        root = tok.split(".", 1)[0]
        depth = tok.count(".") + 1
        if root in KNOWN_ROOTS and depth >= MIN_ANCHOR_DEPTH:
            dangling.append(tok)          # stale reference to this repo
    # Ids that are not dotted would be missed by the token scan; none exist in
    # the current exports, but stay honest about the general case.
    for kid in known_ids:
        if "." not in kid and kid not in anchors and kid in text:
            anchors.append(kid)
    return sorted(set(anchors)), sorted(set(dangling))


def iter_claims(path: str, rel: str):
    """Yield claim dicts for one markdown file, in file order."""
    with open(path, encoding="utf-8", errors="replace") as fh:
        lines = fh.read().splitlines()

    in_fence = False
    for lineno, line in enumerate(lines, 1):
        stripped = line.strip()
        if stripped.startswith("```") or stripped.startswith("~~~"):
            in_fence = not in_fence
            continue
        if in_fence or not stripped:
            continue
        if stripped.startswith("<!--") and stripped.endswith("-->"):
            continue                       # a bare waiver / comment line
        if stripped.startswith("#"):
            continue                       # heading: a title, not an assertion

        narrative = is_narrative_line(line)

        # -- table row -----------------------------------------------------
        cells = table_cells(stripped)
        if cells is not None:
            if is_separator_row(cells):
                continue
            left, right = cells[0], cells[-1]
            # The canonical theorem table: a backticked label on the left and
            # an assertion on the right.
            row_claims = has_ticked_ident(left, loose=True) and bool(right) and not is_separator_row([right])
            # Wider net: any row that carries a backticked ident AND a trigger
            # word in its cells is also asserting a machine fact.
            if not row_claims and any(has_ticked_ident(c) for c in cells):
                row_claims = looks_like_claim(stripped)
            if not row_claims:
                continue
            yield {"rel": rel, "line": lineno, "kind": "table-row",
                   "text": stripped, "narrative": narrative}
            continue

        # -- prose ---------------------------------------------------------
        for sent in split_sentences(stripped):
            if not looks_like_claim(sent):
                continue
            yield {"rel": rel, "line": lineno, "kind": "sentence",
                   "text": sent, "narrative": narrative}


# --------------------------------------------------------------------------
# Classification
# --------------------------------------------------------------------------

def status_of(claim, known_ids):
    """Precedence: dangling > narrative > anchored > unanchored.

    Dangling outranks narrative on purpose: an explicit waiver does not make a
    stale theorem reference true.
    """
    anchors, dangling = classify_tokens(claim["text"], known_ids)
    if dangling:
        status = "dangling"
    elif claim["narrative"]:
        status = "narrative"
    elif anchors:
        status = "anchored"
    else:
        status = "unanchored"
    return status, anchors, dangling


def fix_hints(text: str, known_ids, anchor_set, limit: int = 2):
    """Closest known ids for identifier-ish backticked spans in a claim.

    Mechanical fix: `cost_exact` -> `IUTBridge.ScaleLedger.cost_exact`.
    Suffix matches win outright; otherwise difflib on the full id.
    """
    order = sorted(known_ids)
    hints = []
    for span in TICKED_RE.findall(text):
        span = span.strip()
        if not (DOTTED_RE.fullmatch(span) or BARE_RE.fullmatch(span)):
            continue
        if span.rsplit(".", 1)[-1].lower() in FILE_EXTS:
            continue
        if span in anchor_set:
            continue
        if "." in span and any(i.startswith(span + ".") for i in order):
            # A namespace/module path, not a theorem name: the fix is not a
            # mechanical rename but "cite which theorem of that module".
            continue
        suffix = "." + span
        exact = [i for i in order if i.endswith(suffix)]
        if len(exact) >= 1:
            cands = exact
        else:
            cands = difflib.get_close_matches(span, order, n=limit, cutoff=0.55)
        for c in cands[:limit]:
            entry = {"token": span, "closest": c}
            if len(cands) > limit or len(cands) > 1:
                # Ambiguous: an abbreviated name that several theorems share.
                entry["candidates"] = len(cands)
            if entry not in hints:
                hints.append(entry)
    return hints


def build_index(root: str):
    known_ids, missing = load_fact_trees(root)
    if not known_ids:
        raise SystemExit(
            "claim_index: no fact-tree ids found under %s (looked for: %s)"
            % (root, ", ".join(FACT_TREES))
        )

    docs = []
    for pattern in DOC_GLOBS:
        for path in sorted(_glob(root, pattern)):
            rel = os.path.relpath(path, root).replace(os.sep, "/")
            if rel not in docs:
                docs.append(rel)
    # Deterministic, independent of glob order.
    docs = sorted(docs, key=lambda r: (r.lower(), r))

    files, totals = [], {"claims": 0, "anchored": 0, "narrative": 0,
                         "unanchored": 0, "dangling": 0}
    for rel in docs:
        path = os.path.join(root, rel.replace("/", os.sep))
        per = {"path": rel, "claims": 0, "anchored": 0, "narrative": 0,
               "unanchored": 0, "dangling": 0, "items": []}
        for claim in iter_claims(path, rel):
            status, anchors, dangling = status_of(claim, known_ids)
            per["claims"] += 1
            per[status] += 1
            item = {
                "line": claim["line"],
                "kind": claim["kind"],
                "status": status,
                "text": _snippet(claim["text"], SNIPPET_JSON),
                "anchors": anchors,
            }
            if dangling:
                item["dangling"] = dangling
            if status == "unanchored":
                item["hints"] = fix_hints(item["text"], known_ids, set(anchors))
            per["items"].append(item)
        for k in totals:
            totals[k] += per[k]
        files.append(per)

    return {
        "schema": 1,
        "root_hint": "repo root (absolute paths are not recorded: deterministic output)",
        "fact_trees": list(FACT_TREES),
        "fact_trees_missing": missing,
        "known_ids": len(known_ids),
        "docs_indexed": len(docs),
        "totals": totals,
        "files": files,
    }


def _glob(root: str, pattern: str):
    import glob as _g

    return _g.glob(os.path.join(root, pattern.replace("/", os.sep)))


def _snippet(text: str, limit: int) -> str:
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= limit:
        return text
    return text[: limit - 1] + "\u2026"


# --------------------------------------------------------------------------
# Reporting
# --------------------------------------------------------------------------

def render_text(index, max_list: int, show_hints: bool, strict: bool = False) -> str:
    t = index["totals"]
    out = []
    out.append("claim_index -- claim -> theorem traceability")
    out.append("fact-trees: %d file(s), %d known theorem ids (missing: %s)"
               % (len(index["fact_trees"]) - len(index["fact_trees_missing"]),
                  index["known_ids"],
                  ", ".join(index["fact_trees_missing"]) or "none"))
    out.append("docs indexed: %d" % index["docs_indexed"])
    out.append("")
    out.append("claims %d | anchored %d | narrative %d | UNANCHORED %d | DANGLING %d"
               % (t["claims"], t["anchored"], t["narrative"],
                  t["unanchored"], t["dangling"]))
    out.append("")

    worst = sorted(index["files"], key=lambda f: (-f["unanchored"], f["path"]))
    out.append("per file (by unanchored):")
    width = max([len(f["path"]) for f in index["files"]] + [10])
    shown = [f for f in worst if f["claims"]][:max_list] or index["files"]
    for f in shown:
        out.append("  %-*s  claims %4d  anchored %4d  narrative %3d  unanchored %4d  dangling %3d"
                   % (width, f["path"], f["claims"], f["anchored"],
                      f["narrative"], f["unanchored"], f["dangling"]))
    if len([f for f in worst if f["claims"]]) > len(shown):
        out.append("  ... %d more file(s) in --json"
                   % (len([f for f in worst if f["claims"]]) - len(shown)))
    out.append("")

    dangling = [(f["path"], i) for f in index["files"] for i in f["items"]
                if i["status"] == "dangling"]
    out.append("DANGLING (stale anchor -> hard error): %d" % len(dangling))
    for path, item in dangling[:max_list]:
        out.append("  %s:%d  %s" % (path, item["line"], item["text"]))
        out.append("      unknown id(s): %s" % ", ".join(item.get("dangling", [])))
    if len(dangling) > max_list:
        out.append("  ... %d more in --json" % (len(dangling) - max_list))
    out.append("")

    unanchored = [(f["path"], i) for f in index["files"] for i in f["items"]
                  if i["status"] == "unanchored"]
    # Files are already ordered worst-first.  Within the printed list, surface
    # the mechanically fixable claims (one that already cites an abbreviated id)
    # before the ones that cite nothing at all.
    fixed_first = sorted(unanchored, key=lambda pf: (0 if pf[1].get("hints") else 1,
                                                     pf[0].lower(), pf[1]["line"]))
    fixable = sum(1 for _, i in unanchored if i.get("hints"))
    out.append("UNANCHORED (top %d of %d; %d cite an abbreviated id and are "
               "mechanically fixable via --fix-hints):"
               % (min(max_list, len(unanchored)), len(unanchored), fixable))
    for path, item in fixed_first[:max_list]:
        out.append("  %s:%d  %s" % (path, item["line"], _snippet(item["text"], SNIPPET)))
        if show_hints and item.get("hints"):
            for h in item["hints"]:
                extra = ""
                n = h.get("candidates")
                if n and n > 1:
                    extra = "   (ambiguous: %d known ids share this name)" % n
                out.append("      hint: %s  ->  %s%s" % (h["token"], h["closest"], extra))
    if len(unanchored) > max_list:
        out.append("  ... %d more in --json" % (len(unanchored) - max_list))
    out.append("")

    narrative = [(f["path"], i) for f in index["files"] for i in f["items"]
                 if i["status"] == "narrative"]
    out.append("NARRATIVE (declared waivers, not failures): %d" % len(narrative))
    for path, item in narrative[:max_list]:
        out.append("  %s:%d  %s" % (path, item["line"], _snippet(item["text"], SNIPPET)))

    out.append("")
    if t["dangling"]:
        out.append("FAIL: %d dangling anchor(s) -- docs cite ids the fact-trees do not have." % t["dangling"])
    elif strict and t["unanchored"]:
        out.append("FAIL (--strict): %d unanchored claim(s) -- add an anchor or a "
                   "`<!-- narrative -->` waiver." % t["unanchored"])
    elif t["unanchored"]:
        out.append("OK: no dangling anchors. %d unanchored claim(s) reported but not "
                   "fatal; use --strict to fail on them." % t["unanchored"])
    else:
        out.append("OK: no dangling anchors, no unanchored claims.")
    return "\n".join(out)


# --------------------------------------------------------------------------
# CLI
# --------------------------------------------------------------------------

def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        prog="claim_index.py",
        description="Index machine-fact claims in the documentation and require "
                    "each to be anchored to a theorem id present in a fact-tree.",
        epilog="anchor syntax: name the fully-qualified id, e.g. "
               "`IUTBridge.ScaleLedger.cost_exact`; waive commentary with "
               "`<!-- narrative -->` or the word narrative. "
               "exit 0 = clean, 1 = dangling (or unanchored under --strict), "
               "2 = usage/IO.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--root", default=None,
                        help="repo root to index (default: parent of audit/)")
    parser.add_argument("--json", action="store_true",
                        help="emit the full index as JSON instead of a summary")
    parser.add_argument("--strict", action="store_true",
                        help="also exit non-zero when unanchored claims exist")
    parser.add_argument("--fix-hints", action="store_true",
                        help="print the closest known theorem id for each "
                             "backticked id in an unanchored claim")
    parser.add_argument("--max-list", type=int, default=15,
                        help="cap printed list per section (default 15)")
    args = parser.parse_args(argv)

    root = args.root
    if root is None:
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    root = os.path.abspath(root)
    if not os.path.isdir(root):
        print("claim_index: not a directory: %s" % root, file=sys.stderr)
        return 2

    try:
        index = build_index(root)
    except SystemExit as exc:
        print(str(exc), file=sys.stderr)
        return 2
    except (OSError, json.JSONDecodeError) as exc:
        print("claim_index: %s" % exc, file=sys.stderr)
        return 2

    if args.json:
        payload = dict(index)
        payload.pop("root_hint", None)
        payload["strict"] = bool(args.strict)
        payload["exit_would_be"] = _exit_code(payload, args.strict)
        print(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True))
    else:
        print(render_text(index, max(1, args.max_list), args.fix_hints, args.strict))
    return _exit_code(index, args.strict)


def _exit_code(index, strict: bool) -> int:
    if index["totals"]["dangling"]:
        return 1
    if strict and index["totals"]["unanchored"]:
        return 1
    return 0


if __name__ == "__main__":
    try:
        sys.stdout.reconfigure(encoding="utf-8")
    except Exception:
        pass
    sys.exit(main())
