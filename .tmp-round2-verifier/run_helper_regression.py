"""Run the repaired exporter against the preserved minimal Lean regression."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys
from datetime import datetime, timezone

temporary = Path(__file__).resolve().parent
production = temporary.parent
sys.path.insert(0, str(production / "tools"))
import verify

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

old_facts_path = temporary / "fact-tree/facts.json"
old_facts_hash = sha(old_facts_path)
old_facts = json.loads(old_facts_path.read_text(encoding="utf-8"))
old_export_path = temporary / "tools/Export-round1-preserved.lean"
if not old_export_path.exists():
    shutil.copyfile(temporary / "tools/Export.lean", old_export_path)
shutil.copyfile(production / "tools/Export.lean", temporary / "tools/Export.lean")
lake = shutil.which("lake")
if not lake:
    raise RuntimeError("Lake is unavailable")
args = [lake, "env", "lean", "--json", "-DwarningAsError=true", "tools/Export.lean"]
result = subprocess.run(args, cwd=temporary, text=True, encoding="utf-8",
                        capture_output=True, timeout=300)
process_record = {"command": args, "working_directory": str(temporary),
                  "exit_code": result.returncode, "stdout": result.stdout,
                  "stderr": result.stderr}
(temporary / "verification/helper-export-round2.json").write_text(
    json.dumps(process_record, ensure_ascii=False, indent=2), encoding="utf-8")
verify.check_process(result, "actual temporary Lean helper export")
rows = verify.one_information(result.stdout)
by_id = {row["id"]: row for row in rows}
base = "IUTAudit.Scale.hidden_base"
helper = "IUTAudit.Descent.hiddenHelper"
visible = "IUTAudit.Descent.visible"
catalog = [{"id": base, "source": "IUTAudit/Scale.lean"},
           {"id": visible, "source": "IUTAudit/Descent.lean"}]
verify.validate_catalog(catalog, by_id)
targets = {base, visible}
deps = {name: verify.dependencies_via_helpers(name, by_id, targets) for name in targets}
only_visible = verify.admission_closure({visible}, deps)
both = verify.admission_closure(targets, deps)
assert by_id[helper]["kind"] == "definition", by_id[helper]
assert base in by_id[helper]["constants"], by_id[helper]
assert helper in by_id[visible]["constants"], by_id[visible]
assert deps[visible] == {base}, deps
assert only_visible == set(), only_visible
assert both == targets, both
assert sha(old_facts_path) == old_facts_hash, "Old failure evidence was changed"
record = {
    "schema": 1,
    "generated_utc": datetime.now(timezone.utc).isoformat(),
    "purpose": "Actual Lean elaboration regression for helper dependency compression and admission closure",
    "status": "passed",
    "scope": "Verification engineering only; not an IUT theorem or VS Code admission",
    "synthetic_receipt_notice": "The temporary workspace contains an earlier SYNTHETIC TEST ONLY receipt. It was not used by this regression and is never formal VS Code evidence.",
    "production_receipt_modified": False,
    "old_failure_evidence": {
        "path": str(old_facts_path.relative_to(production)), "sha256": old_facts_hash,
        "preserved": True,
        "admitted_ids": [node["id"] for node in old_facts["nodes"]],
        "edges": old_facts["edges"], "pending_count": old_facts["pending_count"]},
    "implementation_sha256": {
        "tools/verify.py": sha(production / "tools/verify.py"),
        "tools/Export.lean": sha(production / "tools/Export.lean")},
    "temporary_source_sha256": {p: sha(temporary / p) for p in
                                ["IUTAudit/Scale.lean", "IUTAudit/Descent.lean", "IUTAudit.lean"]},
    "process": process_record,
    "actual_elaborated_rows": [by_id[n] for n in [base, helper, visible]],
    "dependency_path": [visible, helper, base],
    "compressed_edge": {"from": base, "to": visible},
    "nearest_catalog_dependencies": {n: sorted(d) for n, d in sorted(deps.items())},
    "eligible_only_visible": [visible], "admitted_only_visible": sorted(only_visible),
    "eligible_both": sorted(targets), "admitted_both": sorted(both),
}
destination = production / "verification/round2-helper-regression.json"
destination.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
print(json.dumps({"status": record["status"], "edge": record["compressed_edge"],
                  "admitted_only_visible": sorted(only_visible), "output": str(destination)},
                 ensure_ascii=True))
