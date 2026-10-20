"""Rebuild, audit kernel-visible dependencies, and enforce the VS Code receipt gate.

Run from any directory: python tools/verify.py
An editor receipt is an attestation of observed UI state, not a cryptographic proof.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "verification"
TREE = ROOT / "fact-tree"
SOURCES = ["IUTAudit/Scale.lean", "IUTAudit/Descent.lean"]
CONTEXT = ["lean-toolchain", "lakefile.toml", "lake-manifest.json", "IUTAudit.lean",
           "tools/EditorCheck.lean"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: str) -> str:
    return hashlib.sha256((ROOT / path).read_bytes()).hexdigest()


def save(path: Path, data: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def run(args: list[str], label: str) -> str:
    result = subprocess.run(args, cwd=ROOT, text=True, encoding="utf-8",
                            errors="replace", capture_output=True, timeout=300)
    save(OUT / f"{label}.json", {"command": args, "exit_code": result.returncode,
                                "stdout": result.stdout, "stderr": result.stderr})
    if result.returncode:
        raise RuntimeError(f"{label} failed: {result.stdout}\n{result.stderr}")
    return result.stdout


def main() -> None:
    OUT.mkdir(exist_ok=True)
    TREE.mkdir(exist_ok=True)
    # Close admission before any work: a failed rebuild must never leave stale facts.
    save(TREE / "facts.json", {"status": "verification_in_progress", "nodes": [], "edges": []})
    (TREE / "graph.dot").write_text("digraph facts {}\n", encoding="utf-8")
    (TREE / "index.md").write_text("# fact-tree\n\nVerification in progress; use facts.json as authority.\n", encoding="utf-8")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("lake is not on PATH")
    version = run([lake, "env", "lean", "--version"], "version").strip()
    if "version 4.34.0," not in version:
        raise RuntimeError(f"unexpected toolchain: {version}")
    run([lake, "build"], "build")
    declarations: dict[str, str] = {}
    for path in SOURCES:
        source = (ROOT / path).read_text(encoding="utf-8")
        namespace = re.search(r"^namespace\s+(\S+)", source, re.M).group(1)
        for name in re.findall(r"^theorem\s+(\w+)", source, re.M):
            declarations[f"{namespace}.{name}"] = path
        output = run([lake, "env", "lean", "--json", "-DwarningAsError=true", path],
                     Path(path).stem.lower())
        # These library files intentionally contain no informational commands.
        if output.strip():
            raise RuntimeError(f"nonempty diagnostics in {path}: {output}")
    output = run([lake, "env", "lean", "--json", "-DwarningAsError=true", "tools/Export.lean"],
                 "export")
    messages = [json.loads(line) for line in output.splitlines() if line.strip()]
    if any(m.get("severity") != "information" for m in messages) or len(messages) != 1:
        raise RuntimeError("unexpected dependency-export diagnostics")
    rows = json.loads(messages[0]["data"])
    by_id = {row["id"]: row for row in rows}
    if set(declarations) - set(by_id):
        raise RuntimeError("an expected theorem is absent from the elaborated environment")
    receipt_path = OUT / "vscode-receipt.json"
    receipt = json.loads(receipt_path.read_text(encoding="utf-8")) if receipt_path.exists() else {}
    context_hashes = {path: digest(path) for path in CONTEXT}
    context_passed = receipt.get("context_sha256") == context_hashes
    accepted, pending = [], []
    for name, path in sorted(declarations.items()):
        row = dict(by_id[name])
        bad = set(row["axioms"]) - ALLOWED_AXIOMS
        if bad:
            raise RuntimeError(f"unapproved axioms in {name}: {sorted(bad)}")
        row.update(source=path, sha256=digest(path), scope="generic_mechanism_model")
        row["depends_on"] = sorted(set(row["constants"]) & set(declarations))
        evidence = receipt.get("files", {}).get(path, {})
        passed = (context_passed and evidence.get("sha256", "").lower() == row["sha256"] and
                  evidence.get("lean_server_checked") is True and
                  evidence.get("errors") == 0 and evidence.get("warnings") == 0 and
                  bool(evidence.get("observation")))
        row["status"] = "admitted" if passed else "pending_vscode"
        (accepted if passed else pending).append(row)
    admitted_ids = {row["id"] for row in accepted}
    if any(set(row["depends_on"]) - admitted_ids for row in accepted):
        raise RuntimeError("an admitted theorem depends on a theorem lacking editor admission")
    edges = [{"from": dep, "to": row["id"]} for row in accepted for dep in row["depends_on"]]
    generated = datetime.now(timezone.utc).isoformat()
    common = {"generated_utc": generated, "lean": version,
              "context_sha256": context_hashes,
              "trust": "Lean kernel plus audited standard axioms; UI receipt is an observation",
              "scope": "Project theorem DAG. Imported library constants are metadata, not admitted nodes.",
              "iut_cor312_proved": False, "abc_proved": False}
    save(OUT / "candidates.json", {**common, "nodes": accepted + pending})
    save(TREE / "facts.json", {**common, "status": "checked", "nodes": accepted, "edges": edges,
                               "pending_count": len(pending)})
    lines = ["digraph facts {", "  rankdir=LR;"]
    for row in accepted:
        lines.append(f'  "{row["id"]}";')
    for edge in edges:
        lines.append(f'  "{edge["from"]}" -> "{edge["to"]}";')
    (TREE / "graph.dot").write_text("\n".join(lines + ["}", ""]), encoding="utf-8")
    index = ["# fact-tree", "", f"已准入 {len(accepted)} 个定理；待 VS Code 验收 {len(pending)} 个。",
             "", "只有通用机制模型。Corollary 3.12 与 abc 均未证明。",
             "", "方向：前提定理 → 使用它的定理。库常量和自动生成辅助项见 candidates.json 元数据。",
             "", "| 定理 | 源文件 | 本项目定理依赖 |", "|---|---|---|"]
    for row in accepted:
        deps = ", ".join(row["depends_on"]) or "无"
        index.append(f'| `{row["id"]}` | `{row["source"]}` | {deps} |')
    (TREE / "index.md").write_text("\n".join(index) + "\n", encoding="utf-8")
    print(f"Lean zero-diagnostic source checks passed. Admitted={len(accepted)}, pending={len(pending)}.")


if __name__ == "__main__":
    main()
