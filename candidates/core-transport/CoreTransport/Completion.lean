import CoreTransport.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

namespace CoreTransport
open scoped Valued
noncomputable section
local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

/-- The height-one prime of `ℤ` attached to the prime number `p`. -/
abbrev rationalPlace (p : Nat.Primes) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := ℤ)).symm p

/-- The valuation-completion construction of the same local field. -/
abbrev RationalCompletion (p : Nat.Primes) := (rationalPlace p).adicCompletion ℚ

/-- A real continuous local-field isomorphism already constructed by Mathlib. -/
def completionArrow (p : Nat.Primes) : ℚ_[p] ≃A[ℚ] RationalCompletion p :=
  Padic.adicCompletionEquiv ℤ p

/-- Both sides are the literal series. This is not definition by conjugation. -/
theorem completion_log_square (p : Nat.Primes) (x : ℚ_[p]) :
    completionArrow p (localLog x) = localLog (completionArrow p x) :=
  localLog_natural (completionArrow p).toRingEquiv
    (completionArrow p).continuous (completionArrow p).symm.continuous x

/-- The integer-ring arrow and the field arrow commute on actual integral elements. -/
theorem completion_integral_square (p : Nat.Primes) (x : ℤ_[p]) :
    ((PadicInt.adicCompletionIntegersEquiv ℤ p x :
      (rationalPlace p).adicCompletionIntegers ℚ) : RationalCompletion p) =
    completionArrow p (x : ℚ_[p]) :=
  PadicInt.coe_adicCompletionIntegersEquiv_apply ℤ p x

/-- On the same arrow, field multiplication is carried along with logarithms. -/
theorem completion_multiplication_square (p : Nat.Primes) (s x : ℚ_[p]) :
    completionArrow p (s * x) = completionArrow p s * completionArrow p x :=
  (completionArrow p).map_mul s x

/-- Root-of-unity orbits are transported by this same arithmetic arrow. -/
theorem completion_torsionOrbit_square (p : Nat.Primes) (n : ℕ) (θ : ℚ_[p]) :
    completionArrow p '' torsionOrbit n θ = torsionOrbit n (completionArrow p θ) :=
  torsionOrbit_transport (completionArrow p).toRingEquiv n θ

end
end CoreTransport

