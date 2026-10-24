import Boundary.DiscreteValuation
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! Concrete instantiation on the canonical completions at finite number-field
places. The field is definitionally the same expression as IUT's completionAt,
but this file does not import or instantiate a Hodge theater. -/
set_option autoImplicit false

namespace CoreFinitePlaceKummer
open scoped WithZero Pointwise
open NumberField IsDedekindDomain KummerTheory CoreDiscreteKummer

variable {K : Type*} [Field K] [NumberField K]

noncomputable abbrev fieldAt (w : FinitePlace K) := w.maximalIdeal.adicCompletion K

noncomputable def localValuation (w : FinitePlace K) : Valuation (fieldAt w) ℤᵐ⁰ := Valued.v

theorem integerRegion_eq (w : FinitePlace K) :
    integerRegion (localValuation w) =
      (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) := rfl

theorem integerRing_isDVR (w : FinitePlace K) :
    IsDiscreteValuationRing (w.maximalIdeal.adicCompletionIntegers K) := inferInstance

theorem mem_principal_iff (w : FinitePlace K) {x : fieldAt w} (hx : x ≠ 0)
    (z : fieldAt w) :
    z ∈ x • (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) ↔
      localValuation w z ≤ localValuation w x :=
  CoreDiscreteKummer.mem_principal_iff (localValuation w) hx z

variable {Ω : Type*} [Field Ω]

theorem principal_eq_of_normalized_kummer_tower (w : FinitePlace K)
    [Algebra (fieldAt w) Ω] [IsGalois (fieldAt w) Ω]
    (m : ℕ) (hm : m ≠ 0) (ell : ℕ) (hell : 1 < ell)
    (roots : ∀ k : ℕ, HasKummerRoots (ell ^ k) (fieldAt w) Ω)
    (x y : (fieldAt w)ˣ)
    (h : ∀ k : ℕ, letI := roots k
      kummer (ell ^ k) (fieldAt w) Ω (x ^ m) =
        kummer (ell ^ k) (fieldAt w) Ω (y ^ m)) :
    (x : fieldAt w) • (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) =
      (y : fieldAt w) • (w.maximalIdeal.adicCompletionIntegers K : Set (fieldAt w)) :=
  CoreDiscreteKummer.principal_eq_of_normalized_kummer_tower
    (localValuation w) m hm ell hell roots x y h

end CoreFinitePlaceKummer

#print axioms CoreFinitePlaceKummer.fieldAt
#print axioms CoreFinitePlaceKummer.localValuation
#print axioms CoreFinitePlaceKummer.integerRegion_eq
#print axioms CoreFinitePlaceKummer.integerRing_isDVR
#print axioms CoreFinitePlaceKummer.mem_principal_iff
#print axioms CoreFinitePlaceKummer.principal_eq_of_normalized_kummer_tower
