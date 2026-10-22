# Restricted model tools

These entry points compute finite, explicitly supplied models and ask Lean to
check the emitted certificate. The Python components only emit `PROPOSED`
claims. The shared runner fixes each component path, Lake project, helper target,
and allowed theorem set; a manifest cannot choose a command or declaration.

## Prerequisites

The runner expects the repository's local sibling worktrees and their locked
Lean dependencies:

* `../iut-wt/m2/candidates/orbit-quotient`
* `../iut-wt/m1/candidates/restricted-ledger`

Each project must have its own `lakefile.toml`, `lake-manifest.json`, and
`lean-toolchain`, with its Candidate helper source present. The projects use
local dependency paths recorded in those files. This is a local workspace
workflow; the components and certificates are not portable to arbitrary Lean
installations. The runner hashes Candidate sources, bridge/local-field Lean
sources, the emitters, and lock/configuration files before and after
verification to reject source drift and stale-build situations. Before Lean,
it recomputes the result and certificate with the fixed emitter and requires an
exact request/result/theorem-name/certificate match. The hashes identify the
exact artifacts; deterministic re-emission and Lean checking bind numeric
claims to the accepted theorem statements.

## Run

From the repository root:

```powershell
python model-tools/run.py hull --input model-tools/examples/hull-swap.json --out $env:TEMP\hull-run
python model-tools/run.py ledger --input model-tools/examples/ledger-two-profiles.json --out $env:TEMP\ledger-run
```

Use a new or empty output directory for each run. The component writes
`request.json`, `result.json`, `certificate.lean`, and `manifest.json`; the
runner retains component, Lake, and Lean stdout/stderr logs plus its verified
manifest/result. The certificate is copied byte-for-byte to
`Candidates/Generated/<sha256>.lean`, a Git-ignored directory for editor use.
The file in the output directory is the original certificate. Their SHA-256
values must match.

Exit codes are `0` for a Lean-checked result (including a proved
counterexample), `2` for insufficient domain data or invalid input, `1` for
component/protocol/Lean failures, and `124` for a bounded timeout. No cache or
skip option can turn an unverified proposal into a verified status. `lake
build` is invoked only with the fixed target for the selected tool, followed
by `lake env lean --json -DwarningAsError=true --stdin`. Required theorem names
are fixed per tool, and their axiom reports may contain only `propext`,
`Classical.choice`, and `Quot.sound`.

## Scope

`hull` handles finite coordinate thresholds over a finite `ZMod (p^N)` box and a
finite list of coordinate permutations. `ledger` handles actual nonzero
`Q_p` tuples whose valuation profiles belong to a user-supplied finite list.
Its domain check is separate from the ledger-preservation check. Neither tool
establishes IUT admissibility, abc, or a result about arbitrary domains.

## 本轮准入边界

`VERIFIED` / `VERIFIED_COUNTEREXAMPLE` 仅表示本次生成的证书通过 Lean
命令行及公理检查。VS Code 的实际零诊断验收仍有未关闭的
`../GAP-tool-round-editor.md`，本轮新增定理尚未进入正式 fact-tree。
本轮交付与独立核验摘要见 `../research/model-tools-closeout-2026-10-22.md`。
