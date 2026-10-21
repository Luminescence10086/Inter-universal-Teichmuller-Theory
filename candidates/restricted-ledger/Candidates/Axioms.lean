import Candidates.RestrictedLedger

/-!
# Axiom export for the restricted-ledger candidate

This file prints the axiom dependencies of every declaration exported by
`Candidates.RestrictedLedger`. It proves nothing on its own and is not part of the
mathematical content; it exists so that a reviewer can check, in a single frozen
command, that the candidate proves its statements from Lean's standard axioms only
(no `sorry`, no `admit`, no new `axiom` declaration, no `native_decide`).

Expected: every printed dependency set is a subset of
`{propext, Classical.choice, Quot.sound}`.

Run from `candidates/restricted-ledger`:

```
lake env lean --json Candidates/Axioms.lean
```
-/

open Candidates.RestrictedLedger

#print axioms Candidates.RestrictedLedger.dot
#print axioms Candidates.RestrictedLedger.dot_add
#print axioms Candidates.RestrictedLedger.dot_sub
#print axioms Candidates.RestrictedLedger.dot_smul
#print axioms Candidates.RestrictedLedger.dot_sum
#print axioms Candidates.RestrictedLedger.dot_single

#print axioms Candidates.RestrictedLedger.integer_span_criterion
#print axioms Candidates.RestrictedLedger.weightedLedger_shift
#print axioms Candidates.RestrictedLedger.restricted_ledger_criterion

#print axioms Candidates.RestrictedLedger.swapWeights
#print axioms Candidates.RestrictedLedger.equalValuationDomain
#print axioms Candidates.RestrictedLedger.equalValuationDomain_nonempty
#print axioms Candidates.RestrictedLedger.vprofile_of_equal_valuation
#print axioms Candidates.RestrictedLedger.vprofile_one_tuple
#print axioms Candidates.RestrictedLedger.vprofile_pTuple
#print axioms Candidates.RestrictedLedger.equalValuationDomain_span
#print axioms Candidates.RestrictedLedger.equalValuationDomain_realises_generator
#print axioms Candidates.RestrictedLedger.swapWeights_not_invariant
#print axioms Candidates.RestrictedLedger.equal_valuation_two_slot_example
#print axioms Candidates.RestrictedLedger.domain_not_preserved_by_slotwise

#print axioms Candidates.RestrictedLedger.nonzeroDomain
#print axioms Candidates.RestrictedLedger.nonzeroDomain_one_mem
#print axioms Candidates.RestrictedLedger.nonzeroDomain_span
#print axioms Candidates.RestrictedLedger.nonzeroDomain_realises_generator
#print axioms Candidates.RestrictedLedger.full_domain_specialization

#print axioms Candidates.RestrictedLedger.swapWeights_budget
#print axioms Candidates.RestrictedLedger.empty_domain_vacuous
