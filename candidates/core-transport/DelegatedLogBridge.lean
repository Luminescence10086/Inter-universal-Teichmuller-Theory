import CoreTransport.Basic
import CoreLog.QpThree

/-!
# Delegated log bridge: two literal logarithms, one series

`CoreTransport.localLog` and `PadicLogVolume.padicLog` are two independently written literal
logarithm series. This file connects them on the actual `ℚ_[3]`, and then feeds the existing
`Q_3` convergence result into the transport tool's own logarithm.

What this file is, and is not:

* Item 1 is **definition-level wiring**, not mathematical content. The two series have the same
  term `(-1)^n (x-1)^{n+1}/(n+1)`; the theorem records that fact in the open, with both
  definitions unfolded, so that no later claim rests on them being secretly different objects.
* Item 2 genuinely consumes the convergence proof (`CoreLog.principal_unit_log_summable`) — the
  `HasSum` statement is derived from summability, not read off `tsum`'s junk default value.
* Item 3 transports the closed-ball image statement through item 1.
* Nothing here constructs a Θ-link, an `Ism`, or anything belonging to IUT; no Galois or
  deformation structure is added, and no new instance is introduced.
-/

namespace DelegatedLogBridge

noncomputable section

open Filter Topology

/-- **Item 1 (definition-level wiring).** On the actual `ℚ_[3]` the transport tool's logarithm
and the `Q_3` logarithm are the same series, term for term. Both definitions are unfolded here:
this is an identification of two existing definitions, not a new function. -/
theorem localLog_eq_padicLog (x : ℚ_[3]) :
    CoreTransport.localLog x = PadicLogVolume.padicLog x := by
  unfold CoreTransport.localLog PadicLogVolume.padicLog PadicLogVolume.logTerm
  rfl

/-- **Item 2a.** The same series is summable on the principal units of `ℚ_[3]`, quoting the
existing `Q_3` convergence result rather than re-proving it. -/
theorem summable_logTerm {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    Summable (PadicLogVolume.logTerm x) :=
  CoreLog.principal_unit_log_summable hx

/-- **Item 2b.** For `‖x - 1‖ < 1` the series sums to `CoreTransport.localLog x`. The proof goes
through summability (`summable_logTerm`), so it depends on the actual convergence argument and
not on the totalized `tsum` default. -/
theorem hasSum_logTerm_localLog {x : ℚ_[3]} (hx : ‖x - 1‖ < 1) :
    HasSum (PadicLogVolume.logTerm x) (CoreTransport.localLog x) := by
  rw [localLog_eq_padicLog x]
  exact (summable_logTerm hx).hasSum

/-- **Item 3.** The transport tool's log image of the principal units of `ℚ_[3]` is exactly the
closed ball of radius `‖3‖ = 1/3`. Derived from the existing closed-ball statement by rewriting
along item 1 only. -/
theorem logImage_Q3_eq_closedBall :
    CoreTransport.logImage ℚ_[3] = {y : ℚ_[3] | ‖y‖ ≤ (3 : ℝ)⁻¹} := by
  have h : CoreTransport.logImage ℚ_[3]
      = PadicLogVolume.padicLog '' {u : ℚ_[3] | ‖u - 1‖ < 1} := by
    unfold CoreTransport.logImage
    have hfun : (CoreTransport.localLog : ℚ_[3] → ℚ_[3]) = PadicLogVolume.padicLog := by
      funext u
      exact localLog_eq_padicLog u
    rw [hfun]
  rw [h, CoreLog.principal_unit_log_image]

end

end DelegatedLogBridge

#print axioms DelegatedLogBridge.localLog_eq_padicLog
#print axioms DelegatedLogBridge.summable_logTerm
#print axioms DelegatedLogBridge.hasSum_logTerm_localLog
#print axioms DelegatedLogBridge.logImage_Q3_eq_closedBall
