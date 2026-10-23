# -*- coding: utf-8 -*-
"""N14 static audit: grade the existing editor receipts for K4, W1-W12 and the
support batch T1-T4, and record why M1-M4 have no editor evidence.

Read-only. Never starts Lean, Lake, a language server or an editor.
Writes audit-data.json and audit-detail.txt next to this script.
Every hash below is computed here from the bytes on disk; nothing is copied
from a delivery record.
"""
import hashlib
import json
import os
import re
from datetime import datetime, timezone

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
CORE = os.path.join("handoffs", "core-backward-2026-10-23")
SUP = os.path.join("handoffs", "core-support-2026-10-22")

# task -> (delivery dir, canonical editor receipt relative to that dir)
LEAN_TASKS = ["K4"] + ["W%d" % i for i in range(1, 13)]
PLAIN_TASKS = ["M1", "M2", "M3", "M4"]

GROUP_RE = re.compile(u"\u5728\u6587\u4ef6\u5939 . \u7684\u6587\u4ef6 (.+?) \u4e2d\u6709 (\\d+) \u4e2a\u95ee\u9898")
AXIOM_RE = re.compile(u"depends on axioms")
DECL_RE = re.compile(u"'([A-Za-z0-9_\\.]+)' depends on axioms")
SEV_ERR = u"\u9519\u8bef"
SEV_WARN = u"\u8b66\u544a"
SEV_INFO = u"\u4fe1\u606f"
NOGOALS = "No goals"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_text(path):
    with open(path, "rb") as fh:
        return fh.read().decode("utf-8", "replace")


def norm(p):
    return p.replace("\\", "/")


def abs_of(rel):
    return os.path.join(ROOT, norm(rel))


def mtime_local(path):
    return datetime.fromtimestamp(os.stat(path).st_mtime,
                                  timezone.utc).astimezone().isoformat()


def capture_ts(text):
    m = re.search(r"captured (\d{4}-\d\d-\d\dT[0-9:\.]+[+-]\d\d:\d\d)", text)
    return m.group(1) if m else ""


def parse_ts(s):
    try:
        return datetime.fromisoformat(s.replace("+0800", "+08:00"))
    except Exception:
        return None


def parse_tree(text):
    out = {"axiom_rows": 0, "axiom_modules": {}, "groups": {}, "error_rows": 0,
           "warning_rows": 0, "info_rows": 0, "no_goals": text.count(NOGOALS),
           "no_info_found": "No info found" in text,
           "server_startup": "Starting Lean language server" in text,
           "abs_paths": [], "window_titles": [], "nodes": ""}
    modcount = {}
    for line in text.splitlines():
        if "### nodes:" in line:
            out["nodes"] = line.strip()
        if "ControlType.Window | " in line:
            out["window_titles"].append(line.split("ControlType.Window | ", 1)[1].strip())
        if "ControlType.Group | " in line:
            cand = line.split("|", 1)[1].strip()
            if cand.lower().endswith(".lean"):
                out["abs_paths"].append(cand)
        if AXIOM_RE.search(line):
            out["axiom_rows"] += 1
            m = DECL_RE.search(line)
            if m:
                mod = m.group(1).split(".")[0]
                modcount[mod] = modcount.get(mod, 0) + 1
        m = GROUP_RE.search(line)
        if m:
            out["groups"][m.group(1)] = int(m.group(2))
        if "ControlType.TreeItem |" in line:
            seg = line.split("|", 1)[1]
            if SEV_ERR in seg:
                out["error_rows"] += 1
            elif SEV_WARN in seg:
                out["warning_rows"] += 1
            elif SEV_INFO in seg:
                out["info_rows"] += 1
    out["axiom_modules"] = modcount
    return out


def delivery(task_dir):
    p = os.path.join(task_dir, "delivery.json")
    if not os.path.exists(p):
        return None, None
    return json.loads(read_text(p)), sha256(p)


def pick_lean_output(dl):
    best = None
    for o in dl.get("outputs", []) or []:
        if isinstance(o, dict) and str(o.get("path", "")).lower().endswith(".lean"):
            best = (norm(str(o["path"])), o.get("sha256", ""))
    return best


def recorded_hash(dl, relpath):
    want = norm(relpath).lower()
    for bucket in ("outputs", "inputs"):
        for o in dl.get(bucket, []) or []:
            if isinstance(o, dict) and norm(str(o.get("path", ""))).lower() == want:
                return o.get("sha256", "")
    return ""


def scan_infoview(task_dir, target_lines):
    d = os.path.join(task_dir, "infoview")
    res = {"dir": norm(os.path.relpath(d, ROOT)) if os.path.isdir(d) else "",
           "files": [], "own_nogoals": 0}
    if not os.path.isdir(d):
        return res
    for name in sorted(os.listdir(d)):
        if not name.endswith(".txt"):
            continue
        p = os.path.join(d, name)
        t = read_text(p)
        head = t.splitlines()[0] if t.splitlines() else ""
        m = re.search(r"attempt at (\S+) \(cursor line (\d+)\)", head)
        decl = m.group(1) if m else ""
        cline = int(m.group(2)) if m else 0
        n_g = t.count(NOGOALS)
        owner = ""
        if cline and 0 < cline <= len(target_lines):
            for i in range(cline - 1, -1, -1):
                mm = re.match(r"\s*(?:theorem|lemma|def|instance|structure|example)\s+([A-Za-z0-9_']+)",
                              target_lines[i])
                if mm:
                    owner = mm.group(1)
                    break
        ok = bool(decl) and decl == owner
        if n_g > 0 and ok:
            res["own_nogoals"] += 1
        res["files"].append({"name": name, "decl": decl, "cursor_line": cline,
                             "no_goals": n_g, "current_line_owner": owner,
                             "same_declaration_now": ok, "sha256": sha256(p)})
    return res


def build(task, tdir, receipt_rel_candidates):
    dl, dl_sha = delivery(tdir)
    rec = {"task": task, "delivery_dir": norm(os.path.relpath(tdir, ROOT)),
           "delivery_exists": dl is not None, "delivery_sha256": dl_sha or ""}
    if dl is None:
        rec.update({"target_file": "", "target_sha256_now": "", "source_sha_match": None,
                    "axiom_rows": 0, "own_axiom_rows": 0, "receipt_exists": False})
        return rec
    rec["declared_status"] = dl.get("status")
    rec["editor_run_flag"] = dl.get("editor_run")
    rec["declared_editor_gate"] = json.dumps(dl.get("gates", {}).get("editor", None),
                                             ensure_ascii=False)
    rec["started_at"] = dl.get("started_at", "")
    lean = pick_lean_output(dl)
    if lean:
        rec["target_file"] = lean[0]
        rec["source_sha_recorded"] = lean[1]
    else:  # T3-style: derive from the CLI argv
        argv = ""
        for c in dl.get("commands", []) or []:
            argv += " ".join(c.get("argv", []) or [])
        m = re.search(r"([A-Za-z0-9_]+\.lean)", argv)
        rec["target_file"] = ("candidates/core-transport/" + m.group(1)) if m else ""
        rec["source_sha_recorded"] = ""
    tpath = abs_of(rec["target_file"]) if rec["target_file"] else None
    rec["target_exists"] = bool(tpath and os.path.exists(tpath))
    if rec["target_exists"]:
        rec["target_sha256_now"] = sha256(tpath)
        rec["target_bytes"] = os.path.getsize(tpath)
        rec["target_mtime"] = mtime_local(tpath)
        rec["target_lines"] = read_text(tpath).splitlines()
    else:
        rec["target_sha256_now"] = ""
        rec["target_bytes"] = 0
        rec["target_mtime"] = ""
        rec["target_lines"] = []
    if rec["target_exists"] and rec["source_sha_recorded"]:
        rec["source_sha_match"] = rec["target_sha256_now"] == rec["source_sha_recorded"]
    elif rec["target_exists"]:
        rec["source_sha_match"] = None
    else:
        rec["source_sha_match"] = None

    # git tracking
    rec["git_tracked"] = None
    rec["receipts"] = []
    chosen = None
    for cand in receipt_rel_candidates:
        ap = os.path.join(tdir, cand)
        if os.path.exists(ap):
            chosen = (cand, ap)
            break
    rec["receipt_exists"] = chosen is not None
    if chosen:
        cand, ap = chosen
        rec["receipt_rel"] = norm(os.path.join(os.path.relpath(tdir, ROOT), cand))
        rec["receipt_sha_now"] = sha256(ap)
        rec["receipt_sha_recorded"] = recorded_hash(dl, rec["receipt_rel"])
        text = read_text(ap)
        tr = parse_tree(text)
        rec["capture_ts"] = capture_ts(text)
        rec["tree"] = tr
        rec["axiom_rows"] = tr["axiom_rows"]
        rec["problem_groups"] = tr["groups"]
        rec["window_title"] = tr["window_titles"][0] if tr["window_titles"] else ""
        rec["error_rows"] = tr["error_rows"]
        rec["warning_rows"] = tr["warning_rows"]
        rec["info_rows"] = tr["info_rows"]
        rec["no_info_found"] = tr["no_info_found"]
        rec["server_startup"] = tr["server_startup"]
        rec["tree_nodes"] = tr["nodes"]
        stem = os.path.splitext(os.path.basename(rec["target_file"]))[0] if rec["target_file"] else ""
        rec["own_module_stem"] = stem
        rec["own_axiom_rows"] = tr["axiom_modules"].get(stem, 0)
        rec["own_group_present"] = stem in tr["groups"] if stem else False
        rec["own_group_declared_count"] = tr["groups"].get(stem) if stem else None
        rec["own_path_in_tree"] = any(stem + ".lean" in p for p in tr["abs_paths"]) if stem else False
        rec["groups_other_files"] = {k: v for k, v in tr["groups"].items() if k != stem}
        # timestamp self-consistency
        cts, mts = parse_ts(rec["capture_ts"]), parse_ts(rec["target_mtime"]) if rec["target_mtime"] else None
        rec["capture_after_source"] = bool(cts and mts and cts > mts)
        rec["capture_before_source_seconds"] = (round((mts - cts).total_seconds())
                                                if (cts and mts and mts > cts) else 0)
        rec["infoview"] = scan_infoview(tdir, rec["target_lines"])
        rec["own_infoview_nogoals"] = rec["infoview"]["own_nogoals"]
    else:
        rec["receipt_sha_now"] = ""
        rec["receipt_sha_recorded"] = ""
        rec["axiom_rows"] = 0
        rec["own_axiom_rows"] = 0
        rec["own_group_present"] = False
        rec["own_infoview_nogoals"] = 0
        rec["capture_ts"] = ""
        rec["capture_after_source"] = None
        rec["infoview"] = {"dir": "", "files": [], "own_nogoals": 0}

    # capture log
    log_abs = os.path.join(tdir, "editor", "vscode-capture-2.log")
    rec["capture_log_rel"] = norm(os.path.relpath(log_abs, ROOT)) if os.path.exists(log_abs) else ""
    rec["capture_log_sha256"] = sha256(log_abs) if os.path.exists(log_abs) else ""
    rec["capture_log_text"] = read_text(log_abs).lstrip(u"\ufeff") if os.path.exists(log_abs) else ""
    return rec


def classify(rec):
    if not rec.get("delivery_exists"):
        return "MISSING", "no delivery record"
    if not rec.get("receipt_exists"):
        if is_lean_task(rec):
            return "MISSING", u"no editor receipt file exists for this task; the editor plane was never captured for %s" % rec["target_file"]
        return "MISSING", u"no editor receipt: this task is a non-Lean analysis task and cites no editor observation at all"
    if rec.get("source_sha_match") is False:
        return "STALE_HASH", u"the source recorded in the delivery (%s) is not the file on disk (%s); re-elaborate and re-capture the current bytes" % (
            rec["source_sha_recorded"][:12], rec["target_sha256_now"][:12])
    if rec.get("receipt_sha_recorded") and rec["receipt_sha_recorded"] != rec["receipt_sha_now"]:
        return "INSUFFICIENT", "the receipt file no longer hashes to what delivery.json cites; re-capture and re-hash"
    if rec.get("own_axiom_rows", 0) > 0 or rec.get("own_group_present"):
        if rec.get("capture_after_source") is False:
            return "STALE_HASH", u"the Problems rows are the file's own, but the capture (%s) is %ss older than the source (%s)" % (
                rec["capture_ts"], rec["capture_before_source_seconds"], rec["target_mtime"])
        return "SUPPORTED_BY_EXISTING_EVIDENCE", u"own-file axiom rows / own-file problem group present at %s for %s" % (
            rec.get("capture_ts"), rec["target_sha256_now"][:12])
    if rec.get("own_infoview_nogoals", 0) > 0:
        return "INSUFFICIENT", u"only per-declaration 'No goals' dumps (own file, %d declarations); no own-file Problems row and no own-file problem group" % rec["own_infoview_nogoals"]
    if rec.get("axiom_rows", 0) == 0:
        return "INSUFFICIENT", u"the cited tree carries no 'depends on axioms' row at all; window-level silence only"
    return "INSUFFICIENT", u"window-level only: every enumerated problem row belongs to another task's file (%s); no own-file row or group" % (
        ", ".join(sorted(rec.get("groups_other_files", {}).keys())) or "n/a")


def is_lean_task(rec):
    return rec["task"] in LEAN_TASKS or rec["task"] == "T3"


def main():
    records = []
    for task in LEAN_TASKS:
        records.append(build(task, os.path.join(ROOT, CORE, task),
                             ["editor/vscode-observation-tree-2.txt"]))
    for task in PLAIN_TASKS:
        records.append(build(task, os.path.join(ROOT, CORE, task), []))
    # support batch
    records.append(build("T1", os.path.join(ROOT, SUP, "T1"), []))
    records.append(build("T2", os.path.join(ROOT, SUP, "T2"), []))
    records.append(build("T3", os.path.join(ROOT, SUP, "T3"),
                         ["after-root/vscode-observation-tree-2.txt",
                          "vscode-observation-tree-2.txt"]))
    records.append(build("T4", os.path.join(ROOT, SUP, "T4"), []))

    for r in records:
        r["status"], r["needed_action"] = classify(r)

    # git tracking, without running anything that touches Lean
    import subprocess
    for r in records:
        if r.get("target_file"):
            p = subprocess.run(["git", "ls-files", "--error-unmatch", r["target_file"]],
                               cwd=ROOT, capture_output=True, text=True,
                               encoding="utf-8", errors="replace")
            r["git_tracked"] = (p.returncode == 0)
            if r["git_tracked"]:
                q = subprocess.run(["git", "log", "-1", "--format=%H %cI", "--", r["target_file"]],
                                   cwd=ROOT, capture_output=True, text=True,
                                   encoding="utf-8", errors="replace")
                r["last_commit_for_file"] = q.stdout.strip()
            else:
                r["last_commit_for_file"] = ""
        else:
            r["git_tracked"] = False
            r["last_commit_for_file"] = ""

    head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                          text=True, encoding="utf-8", errors="replace").stdout.strip()
    branch = subprocess.run(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=ROOT,
                            capture_output=True, text=True, encoding="utf-8",
                            errors="replace").stdout.strip()

    payload = {"generated_by": "handoffs/non-lean-2026-10-23/N14/audit_n14.py",
               "root": ROOT, "git_head": head, "git_branch": branch,
               "records": records}
    here = os.path.dirname(os.path.abspath(__file__))
    with open(os.path.join(here, "audit-data.json"), "w", encoding="utf-8", newline="\n") as fh:
        json.dump(payload, fh, ensure_ascii=False, indent=2)

    lines = []
    w = lines.append
    w("N14 audit detail  HEAD=%s branch=%s" % (head, branch))
    for r in records:
        w("")
        w("=" * 100)
        w("%s  status=%s  declared=%s  editor_run=%s" % (r["task"], r["status"], r.get("declared_status"), r.get("editor_run_flag")))
        w("  target        : %s" % r.get("target_file"))
        w("  sha(recorded) : %s" % r.get("source_sha_recorded"))
        w("  sha(now)      : %s   match=%s  bytes=%s" % (r.get("target_sha256_now"), r.get("source_sha_match"), r.get("target_bytes")))
        w("  mtime(local)  : %s   capture=%s   capture_after_source=%s  lag_s=%s" % (
            r.get("target_mtime"), r.get("capture_ts"), r.get("capture_after_source"), r.get("capture_before_source_seconds")))
        w("  git tracked   : %s   last_commit=%s" % (r.get("git_tracked"), r.get("last_commit_for_file")))
        if r.get("receipt_exists"):
            w("  receipt       : %s" % r["receipt_rel"])
            w("  receipt sha   : now=%s recorded=%s match=%s" % (
                r.get("receipt_sha_now"), r.get("receipt_sha_recorded"),
                r.get("receipt_sha_now") == r.get("receipt_sha_recorded")))
            w("  window        : %s   %s" % (r.get("window_title"), r.get("tree_nodes")))
            w("  rows          : axiom=%s (own=%s, own_group=%s/%s) err=%s warn=%s info=%s" % (
                r.get("axiom_rows"), r.get("own_axiom_rows"), r.get("own_group_present"),
                r.get("own_group_declared_count"), r.get("error_rows"), r.get("warning_rows"), r.get("info_rows")))
            w("  groups        : %s" % json.dumps(r.get("problem_groups"), ensure_ascii=False))
            w("  own path in tree=%s  No info found=%s  server startup text=%s" % (
                r.get("own_path_in_tree"), r.get("no_info_found"), r.get("server_startup")))
            iv = r.get("infoview", {})
            w("  infoview dir  : %s own_nogoals=%s of %s dumps" % (iv.get("dir"), iv.get("own_nogoals"), len(iv.get("files", []))))
            for f in iv.get("files", []):
                w("     %-34s decl=%-40s cursor=%-5s nogoals=%s owner_now=%s match=%s" % (
                    f["name"], f["decl"], f["cursor_line"], f["no_goals"], f["current_line_owner"], f["same_declaration_now"]))
            w("  capture log   : %s" % r.get("capture_log_rel"))
            if r.get("capture_log_text"):
                for ln in r["capture_log_text"].splitlines()[:40]:
                    w("     | " + ln)
        else:
            w("  receipt       : (none)  capture log=%s" % r.get("capture_log_rel"))
        w("  ACTION        : %s" % r.get("needed_action"))

    with open(os.path.join(here, "audit-detail.txt"), "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(lines) + "\n")

    counts = {}
    for r in records:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    print(json.dumps({"counts": counts, "head": head, "branch": branch}, ensure_ascii=False))
    for r in records:
        print("%-3s %-32s own=%-2s all=%-3s groups=%-2s match=%s" % (
            r["task"], r["status"], r.get("own_axiom_rows"), r.get("axiom_rows"),
            len(r.get("problem_groups") or {}), r.get("source_sha_match")))


if __name__ == "__main__":
    main()
