/-
# M2 candidate: complete declaration types and axiom dependencies

Run after compiling Candidates/OrbitQuotient.lean to this project's own olean:
  lake env lean --json -DwarningAsError=true Candidates/Axioms.lean

Every definition, helper lemma and main theorem in the entry is exported below.
Informational output is expected; error and warning diagnostics are not.
-/

import Candidates.OrbitQuotient

set_option pp.universes false
set_option pp.explicit false

#check @OrbitQuotient.Box
#check @OrbitQuotient.IdealBox
#check @OrbitQuotient.permAct
#check @OrbitQuotient.orbitUnion
#check @OrbitQuotient.orbitUnion_eq_inverse_images
#check @OrbitQuotient.hullThresh
#check @OrbitQuotient.pow_mul_pow_sub
#check @OrbitQuotient.le_of_pow_dvd_pow
#check @OrbitQuotient.val_pow_natCast
#check @OrbitQuotient.dvd_iff_val_dvd
#check @OrbitQuotient.IdealBox_eq_Box
#check @OrbitQuotient.box_mono
#check @OrbitQuotient.mem_permAct_box
#check @OrbitQuotient.le_of_box_subset
#check @OrbitQuotient.hull_thresholds
#check @OrbitQuotient.hull_minimal
#check @OrbitQuotient.coordinateProductHull
#check @OrbitQuotient.coordinateProductHull_minimal
#check @OrbitQuotient.coordinateProductHull_orbitUnion
#check @OrbitQuotient.hull_minimal_coordinateProduct
#check @OrbitQuotient.boxFinEquiv
#check @OrbitQuotient.box_cardinality
#check @OrbitQuotient.enlargement_budget
#check @OrbitQuotient.enlargement_budget_hull
#check @OrbitQuotient.kTwo
#check @OrbitQuotient.gammaTwo
#check @OrbitQuotient.gammaTwo_nonempty
#check @OrbitQuotient.gammaTwo_one_mem
#check @OrbitQuotient.gammaTwo_swap_mem
#check @OrbitQuotient.kTwo_zero
#check @OrbitQuotient.kTwo_one
#check @OrbitQuotient.fin_two_cases
#check @OrbitQuotient.zmod_two_two_dvd_iff
#check @OrbitQuotient.zmod_two_eq_one_of_ne_zero
#check @OrbitQuotient.mem_box_kTwo
#check @OrbitQuotient.mem_box_kTwo_swap
#check @OrbitQuotient.orbitUnion_gammaTwo
#check @OrbitQuotient.union_halfspaces_eq_ne
#check @OrbitQuotient.hullThresh_gammaTwo
#check @OrbitQuotient.two_three_four

#print OrbitQuotient.Box
#print OrbitQuotient.IdealBox
#print OrbitQuotient.permAct
#print OrbitQuotient.orbitUnion
#print OrbitQuotient.hullThresh
#print OrbitQuotient.coordinateProductHull

#print axioms OrbitQuotient.Box
#print axioms OrbitQuotient.IdealBox
#print axioms OrbitQuotient.permAct
#print axioms OrbitQuotient.orbitUnion
#print axioms OrbitQuotient.orbitUnion_eq_inverse_images
#print axioms OrbitQuotient.hullThresh
#print axioms OrbitQuotient.pow_mul_pow_sub
#print axioms OrbitQuotient.le_of_pow_dvd_pow
#print axioms OrbitQuotient.val_pow_natCast
#print axioms OrbitQuotient.dvd_iff_val_dvd
#print axioms OrbitQuotient.IdealBox_eq_Box
#print axioms OrbitQuotient.box_mono
#print axioms OrbitQuotient.mem_permAct_box
#print axioms OrbitQuotient.le_of_box_subset
#print axioms OrbitQuotient.hull_thresholds
#print axioms OrbitQuotient.hull_minimal
#print axioms OrbitQuotient.coordinateProductHull
#print axioms OrbitQuotient.coordinateProductHull_minimal
#print axioms OrbitQuotient.coordinateProductHull_orbitUnion
#print axioms OrbitQuotient.hull_minimal_coordinateProduct
#print axioms OrbitQuotient.boxFinEquiv
#print axioms OrbitQuotient.box_cardinality
#print axioms OrbitQuotient.enlargement_budget
#print axioms OrbitQuotient.enlargement_budget_hull
#print axioms OrbitQuotient.kTwo
#print axioms OrbitQuotient.gammaTwo
#print axioms OrbitQuotient.gammaTwo_nonempty
#print axioms OrbitQuotient.gammaTwo_one_mem
#print axioms OrbitQuotient.gammaTwo_swap_mem
#print axioms OrbitQuotient.kTwo_zero
#print axioms OrbitQuotient.kTwo_one
#print axioms OrbitQuotient.fin_two_cases
#print axioms OrbitQuotient.zmod_two_two_dvd_iff
#print axioms OrbitQuotient.zmod_two_eq_one_of_ne_zero
#print axioms OrbitQuotient.mem_box_kTwo
#print axioms OrbitQuotient.mem_box_kTwo_swap
#print axioms OrbitQuotient.orbitUnion_gammaTwo
#print axioms OrbitQuotient.union_halfspaces_eq_ne
#print axioms OrbitQuotient.hullThresh_gammaTwo
#print axioms OrbitQuotient.two_three_four
