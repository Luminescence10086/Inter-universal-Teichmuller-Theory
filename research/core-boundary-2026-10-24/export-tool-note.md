# Frontier declaration export tool

`candidates/core-kummer/ExportFrontier.lean` imports `Lean` and `Boundary.Frontier` and defines an explicit `Array Name` containing every unique declaration name listed by `#print axioms` in the assembled `Boundary/Frontier.lean` at preparation time.

The exporter resolves each selected name with `Environment.find?`. It uses `Environment.getModuleIdxFor?` and the environment module table to identify declarations owned by `Boundary.Frontier`. The graph JSON printed to stdout contains only those local declarations. For each local node it records `id`, defining `module`, declaration `kind`, pretty-printed type as `statement`, and direct `constants` found in the declaration type and, where exposed, value via `Expr.getUsedConstants`.

Traversal starts only from the explicit selected-name array. It recursively follows only referenced constants whose module index is the same as `Boundary.Frontier`, thereby including same-module helpers without scanning `Environment.constants` or all of Mathlib. Referenced external declarations are retained in a node's direct `constants` list but are not traversed into graph nodes.

`KummerTheory.Decomposition.decompositionMap_surjective` is itself present among Frontier's `#print axioms` names, but is defined upstream. The tool resolves and reports it separately on stderr under `UPSTREAM_EXTERNAL_DECLARATIONS=...`; it is excluded from the local graph. This separates provenance from Frontier-authored declarations.

This is a source preparation note only. The exporter has not been compiled or run. No Lean command was run, and the generated JSON has not been validated.
# Parent validation note

The final parent-selected list contains 36 checked names after adding the
explicit coefficient-algebra/action constructions. The exporter ran with exit
0. During command elaboration Lean forwards `IO.eprintln` through its output
channel, so the saved stdout artifact contains exactly two lines: the local
JSON array and `UPSTREAM_EXTERNAL_DECLARATIONS=<JSON array>`. The separate
stderr file is empty. `index.py` validates this exact framing; it does not
discard arbitrary extra diagnostics. The upstream declaration remains outside
the local graph. No per-name collectAxioms or whole-environment scan is used.

