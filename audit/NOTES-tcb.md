# TCB manifest — pin exactly what the verifier reads

**Borrowed discipline.** seLSA/SLSA scope provenance to artifacts that feed a decision;
everything else is failure surface. `audit/tcb_manifest.py` gives each verifier
strace-style discovery (`open`, `read_text`, `json.load`, `glob`, `rglob`, argv of
`subprocess.run`, `import`) plus a call-graph closure from `main()`, then a taint split
strace cannot make: **interpreted** = content changes a decision; **hash-only** =
globbed and hashed *inside the pin builder*, never interpreted — pinned, but unable to
influence any decision.

**Measured** (`--json`, all three projects):

| project | pinned | read (TCB) | over-pinned | under-pinned | admissions |
|---|---|---|---|---|---|
| root | 16 | 13 (11) | 2 | 0 | 38 |
| local-field | 15 | 12 (10) | 2 | 0 | 24 |
| bridge | 36 | 26 (15) | 20 | 0 | 73 |

root / local-field over-pin `tools/query.py` and `.vscode/settings.json` (no read site at
all). bridge over-pins 20 of 36 keys: 15 `@workspace/tools/*`, bridge-local
`tools/{DefinitionBodies,Imports,query_integrated,test_integrated_gate}`, `.vscode/settings.json`;
its `dependency_sha256` map over-pins 14 of 17 (only `external-lock.json` and
`lake-manifest.json` are read, 1 key synthetic). **Under-pinned is empty everywhere** —
the dangerous direction is clean today, all measured cost sits on the brittle side.

**Proposed narrowed pin** (`--propose`; printed, never written): root 14 keys, local-field
13, bridge 16 (13 interpreted + 3 declared toolchain inputs). Recorded hashes equal disk
(`pin_matches_disk: true`), so narrowing disturbs no observation.

**Risk.** bridge pins 36 keys but needs 16: one edit to any of the **19
pinned-but-never-read tool files** voids the schema-3 receipt and drops **all 73
admissions** to `awaiting_editor` — exactly the brittleness already observed.

**Limits.** Dynamic paths (`row['path']`, f-strings) are reported UNRESOLVED and exit 3,
never silently "complete"; here only OLean runtime paths, an empty `.vscode` glob and
external-checkout argv remain, none repo-scoped. Regex-constrained segments resolve by
tree match. Toolchain reads (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`) are
declared, not discovered. Functions never reached from `main()` are listed
(`check_process`, bridge's `snapshot` alias). Sibling modules are followed
(`bridge/tools/verify.py` → `verify_integrated`); `importlib`/`getattr` would be missed.
