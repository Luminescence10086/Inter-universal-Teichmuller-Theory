# Compact joint-threshold criterion — candidate only

This independent Lean project proves an abstract sufficient criterion for gluing
jointly feasible approximate witnesses. It is not an implementation of IUT.

## Verified mathematical interface

For a compact topological space X, closed constraints C_i, an upper-semicontinuous
real-valued score L, and a real number a, assume:

    for every finite s and every epsilon > 0,
      there exists ONE x such that
        x belongs to C_i for every i in s,
        and a - epsilon <= L(x).

Then `CoreCompactness.exists_joint_threshold_of_compact` proves:

    there exists ONE x such that
      x belongs to every C_i, and a <= L(x).

The witness in the assumption may depend on the entire finite family s and epsilon.
It cannot be chosen independently for each constraint i. The hypothesis remains
explicit in the Lean statement; this project does not prove it for IUT data.

`bound_of_joint_near_feasible` adds an upper bound L(x) <= b on these same global
feasible points and concludes a <= b. A continuous-score specialization is also
provided. No Hausdorff assumption or nonemptiness assumption is hidden: the stated
joint hypothesis supplies the needed nonemptiness, including the empty subfamily.

The score conclusion is >= a, not equality to a. An exact eta-value would require
an additional upper bound, or a separately proved allowable downscaling operation
which preserves all constraints. Neither is inferred automatically here.

## Existing Mathlib results used

- `UpperSemicontinuousOn.exists_isMaxOn`: each finite closed feasible region is
  compact, so its score has a maximum; the arbitrary-epsilon hypothesis forces
  that maximum to be at least a.
- `UpperSemicontinuous.isClosed_preimage`: the superlevel set {x | a <= L(x)}
  is closed.
- `IsCompact.inter_iInter_nonempty`: the finite intersection property then supplies
  one point in the score superlevel set and every closed constraint.

This avoids reimplementing compactness or extreme-value machinery.

## Regression against independent selection

`independent_witnesses_do_not_glue` uses the actual finite compact space Bool with
the discrete topology. Its two closed constraints are {false} and {true}; L is the
continuous constant-zero function. Each individual constraint has a score-zero
witness, but no point satisfies both. Therefore individual existential witnesses
cannot substitute for finite JOINT feasibility, even on a compact space.

## Relation to external approximation terminology

The parent review identifies IUT III Remark 3.9.7(ii), printed page 146, as defining
a general set's log-volume via an infimum over measurable supersets. Such an outer
approximation by supersets does not, just from the infimum definition, provide the
common-witness lower near-feasibility assumption used here. This project contains
no theorem converting one kind of approximation to the other.

## Reproduction

Lean: leanprover/lean4:v4.34.0-rc2.
Mathlib: 85e3a25e006c35636f0e53b0e9296caca2685bc0.
The manifest uses the existing local cached Mathlib and dependency paths; no root
project update is required. Run from this directory:

```powershell
lake env lean -DwarningAsError=true CoreCompactness/Joint.lean -o .lake/build/lib/lean/CoreCompactness/Joint.olean
lake env lean -DwarningAsError=true CoreCompactness/Counterexample.lean -o .lake/build/lib/lean/CoreCompactness/Counterexample.olean
lake env lean -DwarningAsError=true CoreCompactness.lean
```

All five theorem declarations have explicit `#print axioms` checks.
No sorry, admit, native_decide, or custom axioms are used.
The candidate has not been admitted into the fact tree; VSCode review is separate.
