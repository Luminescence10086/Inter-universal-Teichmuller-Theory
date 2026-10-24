import Lake
open Lake DSL

/-! T049 isolated Lake project.

No source from the main line is copied or modified. The main line project
`candidates/core-kummer` is consumed as a *read-only path dependency*: only its
package root is added to the search path, so its already-built `.olean` files
are visible, but nothing under it is rebuilt or written by this task.
Mathlib is the pinned path dependency recorded in `handoffs/agent-batch-2026-10-24/baseline.json`.
-/

package «t049» where
  -- Keep every Lake/toolchain scratch artefact inside the task directory.
  buildDir := ".lake"

require mathlib from "C:/Users/18746/Desktop/数竞屠宰场/.lake/packages/mathlib"

/-- The main-line core-kummer oleans, used read-only via `lean_lib` search paths. -/
lean_lib Boundary
lean_lib ContinuousKummerTheory
lean_lib CoreKummer

@[default_target]
lean_lib T049 where
  roots := #[`T049.FinitePlaceNorm]
  moreLeanArgs := #["-DwarningAsError=true"]
