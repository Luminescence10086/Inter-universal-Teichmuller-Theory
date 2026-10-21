import Candidates.PilotShadow

/-!
# Axiom audit for `Candidates.PilotShadow`

This file prints the axioms used by every main result of the candidate. It is not part of the
library root; run it with

`lake env lean Candidates/Axioms.lean`

The permitted whitelist is `propext`, `Classical.choice`, `Quot.sound`. Nothing here constructs a
pilot, a Θ-link, an `Ism`, or any IUT object.
-/

namespace Candidates.PilotShadow

#print axioms relabel_toPadic
#print axioms swap23_eq_labelAction
#print axioms orbit_act
#print axioms orbit_mem_iff
#print axioms orbit_card
#print axioms hull_eq
#print axioms hull_slotVector
#print axioms hull_strict_one_coordinate
#print axioms swap23_moves_profile
#print axioms excess_is_uniform

end Candidates.PilotShadow
