import Lake
open Lake DSL

/-!
# `candidates/ind-relations`

A candidate package for the relation-valued model of the Ind1/Ind2/Ind3 allowed-operations
family over actual `Q_p` tuples.  The package requires the worktree's `bridge` package
(`../../bridge`, whose Lake name is `iut_bridge`) exactly as `candidates/pilot-shadow`
does, so that the candidate is built against the same Mathlib lock.
-/

package ind_relations where
  version := v!"0.1.0"
  description := "Relation-valued Ind1-3 allowed operations: Allowed12 ⊊ ambient A(k) toy model"

@[default_target]
lean_lib Candidates

-- The bridge package lives in `../../bridge`.  Lake binds a required package under the
-- *declared* package name of that directory, which is `iut_bridge` (see
-- `bridge/lakefile.toml`); writing `require bridge from "../../bridge"` is rejected with
-- "dependency 'bridge' not in manifest".  This is therefore the exact form of the
-- required `require bridge from "../../bridge"` statement.
require iut_bridge from "../../bridge"
