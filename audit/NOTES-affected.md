# NOTES — `audit/affected.py` (incremental review scoping)

## Analogy: build cache → observation cache (the cache is a receipt, not an object file)

`build target` → an admitted fact-tree node · `source file` → `*.lean`, `tools/*`, toolchain /
lakefile / manifest · `action cache key` → `input_sha256` / `dependency_sha256` /
`evidence_sha256` · `dirty target` → node re-verify **+ re-observe** (source changed, or a
transitive dependency did) · `cache invalidated` → receipt **void**, so every admitted node of
that project → **pending** · `reverse deps` → `depends_on` + `edges`, and schema-3
`dependency_sha256` across projects · `path filters / affected targets` → this tool.
"Rebuild" here is a verifier run plus a fresh editor pass; nothing compiles to a cached object.

## Establishes

Which recorded evidence cannot cover a change set: receipt voids with the exact pin key, nodes
falling back to pending, nodes and transitive dependents needing a new observation, contracts
losing an endpoint, prose-only changes — plus the counts a manual audit would assemble.

## Does NOT establish

1. **Meaning.** It never reads a statement: a byte change may preserve meaning, and a dependency
   change can alter it. Only the statement lock decides — `tools/semantic_lock.py` against
   `bridges/statement-lock.json` / `integrated-lock.json`. This tool only locates how many pinned
   names live in the touched files.
2. **Bytes.** It trusts recorded pins and never hashes; recorded-vs-HEAD bytes belong to
   `bridges/check_clean_checkout.py`.
3. **Truth of the mathematics.** A valid receipt is an observation, not a proof certificate.
4. **Sub-file granularity.** `node.sha256` equals the source-file digest in all three projects.

## Residual risks

- Renames rely on `git -M` (below threshold: delete+add — safe, both sides reported); uncommitted
  edits are invisible to `--range`/`--staged`, pass them with `--files`.
- Absolute `dependency_sha256` keys are anchored on the repository directory name; after a
  rename/move they surface as unresolved pins (errs toward "review", never "clean").
- `@workspace/` pins exist only for the schema-3 bridge receipt and main's recorded input set is
  older/narrower: a root `tools/*.py` edit voids bridge but not main — true to the records, but
  do not over-read "main INTACT".
- Lock-ledger or contract-record edits flag contracts as review-only; they void no receipt.
- Docs are classified by suffix/directory, so a `*.md` carrying evidence would be under-reported.
