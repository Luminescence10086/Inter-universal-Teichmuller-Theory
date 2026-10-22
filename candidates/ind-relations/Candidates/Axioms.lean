import Candidates.IndRelations

/-!
# Axiom audit for `Candidates.IndRelations`

Prints the axioms used by every result of the candidate.  It is not part of the library root;
run it with

`lake env lean Candidates/Axioms.lean`

The permitted whitelist is `propext`, `Classical.choice`, `Quot.sound`.  Nothing here
constructs a Θ-link, an `Ism`, or any IUT object.
-/

namespace Candidates.IndRelations

#print axioms neg_one_ne_one
#print axioms neg_one_ne_zero
#print axioms relabel_relabel
#print axioms scale_scale
#print axioms scale_relabel
#print axioms relabel_single
#print axioms scale_single
#print axioms move_e
#print axioms neg_e
#print axioms move_apply
#print axioms move_projection
#print axioms move_projection_source
#print axioms move_move
#print axioms mem_Gamma12
#print axioms gamma12_trans_mem
#print axioms mem_S
#print axioms flip0_val_zero
#print axioms flip0_val_one
#print axioms allowed12_subset
#print axioms ambient_e3_e2
#print axioms not_allowed12_e3_e2
#print axioms allowed12_strict
#print axioms compositionClosed_of_closed
#print axioms not_scaling_family_closed
#print axioms not_compositionClosed

end Candidates.IndRelations
