import Candidates.Nonarchimedean

/-!
# Axiom audit for `Candidates.Nonarchimedean`

Prints the axioms used by every declaration of the candidate. Run with

`lake env lean Candidates/Axioms.lean`

Permitted whitelist: `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`,
`opaque` or `native_decide` occurs anywhere in this candidate.
-/

namespace Candidates.Nonarchimedean

#print axioms instNonarchimedeanRingPadic
#print axioms exists_openAddSubgroup_subset_closedBall
#print axioms nonarchimedeanAddGroup
#print axioms norm_add_le_max
#print axioms isUltrametricDist
#print axioms hasSum_mul
#print axioms summable_mul
#print axioms tsum_mul_tsum
#print axioms summable_iff_tendsto_cofinite_zero

end Candidates.Nonarchimedean
