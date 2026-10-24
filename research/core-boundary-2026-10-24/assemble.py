"""Produce one reviewable Lean entry point; no theorem text is rewritten."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "candidates/core-kummer/Boundary"
ORDER = ["DiscreteValuation", "FinitePlace", "ReducedComparison", "PrecisionLoss",
         "DecompositionBridge", "LaurentPoint"]
parts, inputs = [], {}
imports = []
for name in ORDER:
    path = BASE / f"{name}.lean"
    inputs[path.relative_to(ROOT).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
    body = []
    for line in path.read_text(encoding="utf-8-sig").splitlines():
        if line.startswith("import "):
            module = line.removeprefix("import ").strip()
            if not module.startswith("Boundary.") and module not in imports:
                imports.append(module)
        else:
            body.append(line)
    parts.append(f"/- Source section: Boundary/{name}.lean -/\n" + "\n".join(body).strip())
text = "\n".join(f"import {m}" for m in imports) + "\n\n" + "\n\n".join(parts) + "\n"
output = BASE / "Frontier.lean"
if not output.exists() or output.read_text(encoding="utf-8-sig") != text:
    output.write_text(text, encoding="utf-8")
(Path(__file__).parent / "assembly.json").write_text(json.dumps({
    "purpose": "Single Lean/editor entry, preserving source-section theorem text",
    "input_sha256": inputs, "imports": imports,
    "output": "candidates/core-kummer/Boundary/Frontier.lean",
    "output_sha256": hashlib.sha256(output.read_bytes()).hexdigest()}, indent=2)+"\n",encoding="utf-8")
print("assembled Frontier.lean")
