/-
# Axiom export for the M2 candidate

Prints the axiom dependencies of every main theorem and of the box/ideal
equivalence lemma of `Candidates/OrbitQuotient.lean`.  The expected output is
contained in `{propext, Classical.choice, Quot.sound}`; in fact no declaration
below uses more than `propext` and `Classical.choice` (Mathlib's classical
decidability and `Finset`/`Nat.card` API).

Run from `candidates/orbit-quotient` with:

  `lake env lean --json Candidates/Axioms.lean`

(requires the library to be built first, i.e. `lake build`, so that the
`Candidates.OrbitQuotient` olean exists).
-/

import Candidates.OrbitQuotient

#print axioms OrbitQuotient.IdealBox_eq_Box
#print axioms OrbitQuotient.hull_thresholds
#print axioms OrbitQuotient.hull_minimal
#print axioms OrbitQuotient.box_cardinality
#print axioms OrbitQuotient.enlargement_budget
#print axioms OrbitQuotient.enlargement_budget_hull
#print axioms OrbitQuotient.two_three_four
