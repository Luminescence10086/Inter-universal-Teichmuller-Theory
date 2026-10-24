# Frozen unfinished obligations

The actual integer-ring iff and derived principal-region theorem below did not compile. Lean inferred two non-definitionally-equal integer algebra instances on the completion integer ring. They are excluded from Completion.lean and from certified exports. The earlier integer-ring commuting square did compile.

```lean
set_option backward.isDefEq.respectTransparency.types false in
/-- The field arrow carries exactly the actual valuation ring. -/
theorem completion_integral_iff (p : Nat.Primes) (x : ℚ_[p]) :
    completionArrow p x ∈ (rationalPlace p).adicCompletionIntegers ℚ ↔
    x ∈ PadicInt.subring p := by
  constructor
  · intro hx
    let y : (rationalPlace p).adicCompletionIntegers ℚ := ⟨completionArrow p x, hx⟩
    obtain ⟨a, ha⟩ := (PadicInt.adicCompletionIntegersEquiv ℤ p).toEquiv.surjective y
    have hae : completionArrow p (a : ℚ_[p]) = completionArrow p x :=
      (completion_integral_square p a).symm.trans (congrArg Subtype.val ha)
    have hax : (a : ℚ_[p]) = x := (completionArrow p).toEquiv.injective hae
    rw [← hax]
    exact a.property
  · intro hx
    rw [← completion_integral_square p ⟨x, hx⟩]
    exact (PadicInt.adicCompletionIntegersEquiv ℤ p ⟨x, hx⟩).property
/-- A principal integral region is transported with the same field arrow and generator. -/
theorem completion_principalRegion_square (p : Nat.Primes) (θ : ℚ_[p]) :
    completionArrow p '' principalRegion (PadicInt.subring p) θ =
    principalRegion ((rationalPlace p).adicCompletionIntegers ℚ).toSubring
      (completionArrow p θ) :=
  principalRegion_transport (completionArrow p).toRingEquiv _ _
    (completion_integral_iff p) θ

end
end CoreTransport



```
