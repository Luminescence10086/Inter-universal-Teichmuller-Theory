"""T015 re-verification: live read-only re-check of the T015 target.

Records the current repository state into logs/reverify.{stdout,stderr}.log and appends a
one-line verdict to logs/reverify-history.log, so the T015 claim can be checked against
files instead of a transcription.

Split of assertions, deliberately kept apart:
  * LOCAL assertions (always run): the reviewed commit still resolves to the same object,
    the local branch and the remote-tracking ref both still point at it, and the two refs
    still agree with each other. These decide the verdict.
  * NETWORK assertion (may be unreachable): does the live remote still carry it? When the
    network is down this is reported as UNRESOLVED with the reason, NOT as a failure --
    an unreachable remote is not evidence that the remote moved.

READ-ONLY. Every git invocation is a query. The only network command is `git ls-remote`
(contact only; writes no refs, no objects, no FETCH_HEAD). No fetch, no checkout, no
reset, no merge, no branch switch.

Exit code 0 = all LOCAL assertions hold (network status is reported, not gated);
           1 = at least one LOCAL assertion failed.

Usage: python reverify.py [--skip-network]
"""
import datetime
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LOGDIR = HERE / "logs"

REVIEWED = "d3c5599668aa57c5c00244117abd26787fcd559e"
BASELINE = "8d60456043e30a3da79cc838d03a19b80675dc98"
REVIEWED_TREE = "731cdae8a42f46a13d38a47f3cd5be0d06bad580"
LAYER5_BLOB = "adc280bef846ca1e49b3a7b7071caaa725221797"
LAYER5_PATH = "research/core-backward-2026-10-23/backward-paths-layer5-2026-10-23.md"
BASELINE_JSON_SHA = "e24e6801c2eac58f7d97cfe5f3f7a95deeaf05852231006a0085290eecd126cf"
BRANCH = "research/backward-paths"

out_lines, err_lines, failures = [], [], []
network_note = ""


def git(*argv, timeout=60):
    try:
        proc = subprocess.run(["git", "-C", str(ROOT), *argv], capture_output=True,
                              text=True, encoding="utf-8", errors="replace",
                              timeout=timeout)
        code, stdout, stderr = proc.returncode, proc.stdout or "", proc.stderr or ""
    except subprocess.TimeoutExpired:
        code, stdout, stderr = 124, "", f"timed out after {timeout}s"
    out_lines.append(f"$ git -C <root> {' '.join(argv)}   # exit={code}")
    body = stdout.rstrip("\n")
    if body:
        out_lines.append(body)
    if stderr.strip():
        err_lines.append(f"$ git {' '.join(argv)}   # exit={code}")
        err_lines.append(stderr.rstrip("\n"))
    out_lines.append("")
    return code, body, stderr


def check(label, actual, expected):
    if actual == expected:
        out_lines.append(f"[ OK ] {label} = {actual}")
        return
    out_lines.append(f"[FAIL] {label} = {actual!r} (expected {expected!r})")
    failures.append(f"{label}: got {actual!r} expected {expected!r}")


def main():
    global out_lines, err_lines, failures
    out_lines, err_lines, failures = [], [], []
    skip_network = "--skip-network" in sys.argv
    network_note = ""
    stamp = datetime.datetime.now().astimezone().isoformat(timespec="seconds")
    out_lines.append("== T015 re-verification :: read-only re-check ==")
    out_lines.append(f"root={ROOT}")
    out_lines.append(f"when={stamp}")
    out_lines.append("")

    # --- 0. baseline file identity ---
    bsha = hashlib.sha256((ROOT / "handoffs/agent-batch-2026-10-24/baseline.json").read_bytes()).hexdigest()
    check("baseline.json sha256", bsha, BASELINE_JSON_SHA)

    # --- 1. current workspace state (disclosed; NOT the T015 target) ---
    _, head, _ = git("rev-parse", "HEAD")
    _, branch, _ = git("rev-parse", "--abbrev-ref", "HEAD")
    out_lines.append(f"[INFO] current HEAD   = {head}")
    out_lines.append(f"[INFO] current branch = {branch}")
    rc, _, _ = git("merge-base", "--is-ancestor", BASELINE, "HEAD")
    out_lines.append(f"[INFO] baseline {BASELINE[:9]} is ancestor of HEAD: {rc == 0} (exit={rc})")
    _, dirty, _ = git("status", "--porcelain", "--untracked-files=no")
    dirty_count = len([x for x in dirty.splitlines() if x.strip()])
    out_lines.append(f"[INFO] tracked dirty files now = {dirty_count} "
                     f"(replay.ps1 pinned the 2026-10-24T13:27 state: 4)")
    out_lines.append("")

    # --- 2. LOCAL: reviewed commit object identity ---
    _, revc, _ = git("rev-parse", f"{REVIEWED}^{{commit}}")
    check("reviewed commit", revc, REVIEWED)
    _, revt, _ = git("rev-parse", f"{REVIEWED}^{{tree}}")
    check("reviewed tree", revt, REVIEWED_TREE)
    _, blob, _ = git("rev-parse", f"{REVIEWED}:{LAYER5_PATH}")
    check("layer5 blob oid", blob, LAYER5_BLOB)
    _, size, _ = git("cat-file", "-s", f"{REVIEWED}:{LAYER5_PATH}")
    check("layer5 blob size (bytes)", size, "9132")

    # --- 3. LOCAL: the two branch refs still coincide ---
    _, lb, _ = git("rev-parse", f"refs/heads/{BRANCH}")
    check("local refs/heads/" + BRANCH, lb, REVIEWED)
    _, tb, _ = git("rev-parse", f"refs/remotes/origin/{BRANCH}")
    check("remote-tracking origin/" + BRANCH, tb, REVIEWED)
    _, refs, _ = git("for-each-ref", "--points-at", REVIEWED, "--format=%(refname)")
    out_lines.append(f"[INFO] refs pointing at reviewed commit: {refs.replace(chr(10), ', ')}")
    _, fw, _ = git("rev-list", "--count", f"refs/heads/{BRANCH}..refs/remotes/origin/{BRANCH}")
    check("new commits remote-tracking-side (reviewed..origin)", fw, "0")
    _, bw, _ = git("rev-list", "--count", f"refs/remotes/origin/{BRANCH}..refs/heads/{BRANCH}")
    check("new commits reviewed-side (origin..reviewed)", bw, "0")
    _, st, _ = git("diff", "--stat", f"refs/remotes/origin/{BRANCH}", f"refs/heads/{BRANCH}")
    check("diff --stat origin vs reviewed", st, "")
    _, fulldiff, _ = git("diff", f"refs/remotes/origin/{BRANCH}", f"refs/heads/{BRANCH}")
    check("full diff origin vs reviewed (bytes)", len(fulldiff), 0)
    out_lines.append("")

    # --- 4. NETWORK: does the live remote still carry this commit? ---
    remote_live, remote_status = "", "UNRESOLVED"
    if skip_network:
        remote_status = "SKIPPED"
        network_note = "--skip-network given; live remote head not contacted in this run."
        out_lines.append("[SKIP] network assertion (--skip-network)")
    else:
        rc, ls, lserr = git("ls-remote", "origin", f"refs/heads/{BRANCH}", timeout=90)
        if rc == 0 and "\t" in ls:
            remote_live = ls.split("\t")[0].strip()
            remote_status = "LIVE"
            check("remote HEAD (live) == reviewed commit", remote_live, REVIEWED)
        else:
            remote_status = "UNRESOLVED"
            reason = (lserr.strip().splitlines() or ["no diagnostic"])[0]
            network_note = f"git ls-remote failed (exit {rc}): {reason}"
            out_lines.append(f"[WARN] live remote check UNRESOLVED -- {network_note}")
            out_lines.append("[NOTE] an unreachable remote is not evidence that the remote moved;")
            out_lines.append("       the local remote-tracking ref remains the last contacted value.")
    out_lines.append(f"[INFO] remote live status = {remote_status}"
                     + (f" ({remote_live})" if remote_live else ""))
    out_lines.append("")

    # --- 5. historical shape of the reviewed commit (unchanged facts) ---
    _, ds, _ = git("diff", "--stat", f"{REVIEWED}^", REVIEWED)
    out_lines.append(f"[INFO] reviewed commit own diff --stat: {ds}")
    _, dt, _ = git("diff-tree", "-r", "--no-commit-id", "--name-status", f"{REVIEWED}^", REVIEWED)
    out_lines.append(f"[INFO] reviewed commit own diff-tree (-r): {dt}")
    _, ns, _ = git("diff-tree", "-r", "--no-commit-id", "--numstat", f"{REVIEWED}^", REVIEWED)
    out_lines.append(f"[INFO] reviewed commit own numstat: {ns}")
    _, meta, _ = git("log", "-1", "--format=%H%n%an%n%ad%n%s", "--date=iso", REVIEWED)
    out_lines.append("[INFO] reviewed commit meta:")
    out_lines.extend(f"         {line}" for line in meta.splitlines())
    _, base_stat, _ = git("diff", "--stat", BASELINE, REVIEWED)
    out_lines.append(f"[INFO] baseline..reviewed diff --stat: {base_stat}")
    out_lines.append("")

    # --- verdict ---
    out_lines.append("")
    code = 0
    if failures:
        out_lines.append(f"T015_REVERIFY_FAIL: {len(failures)} local assertion(s) failed")
        out_lines.extend(f"  - {item}" for item in failures)
        code = 1
        verdict = "FAIL"
    elif remote_status == "LIVE":
        out_lines.append(f"T015_REVERIFY_PASS: remote {BRANCH} == {REVIEWED} "
                         f"(0 new commits; empty diff)")
        verdict = "PASS"
    else:
        out_lines.append(f"T015_REVERIFY_LOCAL_ONLY: all local assertions hold; live remote "
                         f"check {remote_status}. Last contacted remote-tracking value "
                         f"origin/{BRANCH} == {REVIEWED}.")
        verdict = f"LOCAL_ONLY({remote_status})"

    LOGDIR.mkdir(parents=True, exist_ok=True)
    (LOGDIR / "reverify.stdout.log").write_text("\n".join(out_lines) + "\n", encoding="utf-8")
    (LOGDIR / "reverify.stderr.log").write_text(
        "\n".join(err_lines) + ("\n" if err_lines else ""), encoding="utf-8")
    with (LOGDIR / "reverify-history.log").open("a", encoding="utf-8") as fh:
        fh.write(f"{stamp}\tverdict={verdict}\tremote={remote_status}"
                 f"{'=' + remote_live if remote_live else ''}\t"
                 f"head={head}\tdirty={dirty_count}\n")

    print(json.dumps({"result": verdict, "failures": failures, "remote_status": remote_status,
                      "remote_live": remote_live, "reviewed": REVIEWED, "head_now": head,
                      "dirty_now": dirty_count, "network_note": network_note}))
    return code


if __name__ == "__main__":
    sys.exit(main())
