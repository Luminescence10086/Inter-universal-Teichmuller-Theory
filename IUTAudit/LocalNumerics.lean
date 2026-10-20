import Std

/-!
# Exact discrete checks for a proposed local non-containment mechanism

Integer weights use units of 1/105. The constants are taken from the arithmetic
subproblem of Urahigashi's 2026-10-05 draft, tag v0.8.0. This file verifies only
the explicitly written integer identities and a conditional transport argument.
It does not establish primality, initial theta data, local fields, tensor-product
valuation additivity, membership in the IUT pilot region, or the Ind1 action.
Those are separate semantic obligations, not hidden assumptions of a theorem.
-/

set_option autoImplicit false

namespace IUTAudit.LocalNumerics

/-- Integer-indexed strict layers of a discretely represented measurement. -/
def PreservesLayers {X : Type} (step : Int) (v : X → Int) (f : X → X) : Prop :=
  ∀ (n : Int) (x : X), step * n < v (f x) ↔ step * n < v x

/-- Preservation of strict layers also preserves the complementary upper bounds. -/
theorem layer_preserves_upper {X : Type} (step : Int) (v : X → Int) (f : X → X)
    (hf : PreservesLayers step v f) (n : Int) (x : X) (hx : v x ≤ step * n) :
    v (f x) ≤ step * n := by
  by_cases h : v (f x) ≤ step * n
  · exact h
  · have hbad := (hf n x).1 (by omega)
    omega

/-- A measurement remains in the same half-open band if every layer is preserved. -/
theorem layer_preserves_band {X : Type} (step : Int) (v : X → Int) (f : X → X)
    (hf : PreservesLayers step v f) (n : Int) (x : X)
    (hx : step * (n - 1) < v x ∧ v x ≤ step * n) :
    step * (n - 1) < v (f x) ∧ v (f x) ≤ step * n := by
  exact ⟨(hf (n - 1) x).2 hx.1, layer_preserves_upper step v f hf n x hx.2⟩

/-- These finite arithmetic checks do not assert primality or the existence of
the claimed number-field and elliptic-curve data. -/
theorem datum_integer_checks :
    (14164 : Int)^2 - 5 * 5825^2 = 30965771 ∧
    (30965771 : Nat) % 5 = 1 ∧ (30965771 : Nat) % 4 = 3 ∧
    2^12 * 3^3 * 5 * 2 * 7 = (7741440 : Nat) ∧
    (7741440 : Nat) < 30965771 := by
  decide

/-- All denominators have been cleared. The candidate offsets are
`aI = 2/35 = 6/105` and `bI = -2/35 = -6/105`; the candidate module cut is
`floor((810 - 414 - 6)/105) * 105 + 6 = 321` in units of `1/105`.
These are exact arithmetic checks, not verification of the parameters' semantic
origin or of any real logarithm or volume. -/
theorem local_integer_checks :
    (9 : Int) * 15 = 135 ∧ 9 * 90 = (810 : Int) ∧
    3 * 104 + 102 = (414 : Int) ∧
    (2 : Int) * 105 = 6 * 35 ∧ (-2 : Int) * 105 = (-6) * 35 ∧
    (810 - 414 - 6 : Int) = 390 ∧
    ((810 - 414 - 6 : Int) / 105) = 3 ∧
    ((810 - 414 - 6 : Int) / 105) * 105 + 6 = 321 ∧
    (-810 + 414 + 105 : Int) = -3 * 97 ∧
    (-2 * 35 : Int) - (-97) = 27 := by
  decide

/-- Substituting `135` gives the candidate module cut
`floor((135 - 414 - 6)/105) * 105 + 6 = -309`.
The displayed linear allowance increases by `675/105 = 45/7`, while the
floor-rounded module cut changes by `630/105 = 6`. These are different costs.
This arithmetic does not establish an IUT volume estimate or the semantic
validity of the substituted source weight. -/
theorem repaired_cut_and_cost :
    (135 - 414 - 6 : Int) = -285 ∧
    ((135 - 414 - 6 : Int) / 105) = -3 ∧
    ((135 - 414 - 6 : Int) / 105) * 105 + 6 = -309 ∧
    (-135 + 414 + 105 : Int) = 3 * 128 ∧
    (-135 + 414 + 105 : Int) - (-810 + 414 + 105) = 675 ∧
    (675 : Int) * 7 = 45 * 105 ∧
    (321 : Int) - (-309) = 630 ∧ (630 : Int) = 6 * 105 := by
  decide

/-- Under explicit layer preservation, the sum of four measured factors stays
at most `210/105`, excluding the proposed cutoff `321/105`.
The factors may have different underlying
types. The sum is just an integer sum, not an asserted tensor valuation. -/
theorem transformed_sum_excludes_cut
    (X : Fin 4 → Type) (v : (i : Fin 4) → X i → Int)
    (f : (i : Fin 4) → X i → X i) (x : (i : Fin 4) → X i)
    (hf : ∀ i, PreservesLayers 105 (v i) (f i))
    (h0 : v 0 (x 0) = 0) (h1 : v 1 (x 1) = 0)
    (h2 : v 2 (x 2) = 135) (h3 : v 3 (x 3) = 0) :
    ¬ 321 ≤ v 0 (f 0 (x 0)) + v 1 (f 1 (x 1)) +
      v 2 (f 2 (x 2)) + v 3 (f 3 (x 3)) := by
  have b0 := layer_preserves_upper 105 (v 0) (f 0) (hf 0) 0 (x 0) (by omega)
  have b1 := layer_preserves_upper 105 (v 1) (f 1) (hf 1) 0 (x 1) (by omega)
  have b2 := layer_preserves_upper 105 (v 2) (f 2) (hf 2) 2 (x 2) (by omega)
  have b3 := layer_preserves_upper 105 (v 3) (f 3) (hf 3) 0 (x 3) (by omega)
  omega

/-- In the same explicit four-factor measurement model the sum is greater than
`-210/105`, so the weaker cutoff `-309/105` does contain every layer-preserving
image. This certifies only this conditional
repair; it does not provide an action or a global estimate in IUT. -/
theorem transformed_sum_inside_repaired_cut
    (X : Fin 4 → Type) (v : (i : Fin 4) → X i → Int)
    (f : (i : Fin 4) → X i → X i) (x : (i : Fin 4) → X i)
    (hf : ∀ i, PreservesLayers 105 (v i) (f i))
    (h0 : v 0 (x 0) = 0) (h1 : v 1 (x 1) = 0)
    (h2 : v 2 (x 2) = 135) (h3 : v 3 (x 3) = 0) :
    -309 ≤ v 0 (f 0 (x 0)) + v 1 (f 1 (x 1)) +
      v 2 (f 2 (x 2)) + v 3 (f 3 (x 3)) := by
  have b0 := layer_preserves_band 105 (v 0) (f 0) (hf 0) 0 (x 0) (by omega)
  have b1 := layer_preserves_band 105 (v 1) (f 1) (hf 1) 0 (x 1) (by omega)
  have b2 := layer_preserves_band 105 (v 2) (f 2) (hf 2) 2 (x 2) (by omega)
  have b3 := layer_preserves_band 105 (v 3) (f 3) (hf 3) 0 (x 3) (by omega)
  omega

/-- Merely fixing the total allowance does not guarantee allowance in each
component. This finite obstruction matters when proposing averaged repairs. -/
theorem aggregate_bound_does_not_imply_componentwise :
    ¬ (∀ (x y a b : Nat), x + y ≤ a + b → x ≤ a ∧ y ≤ b) := by
  intro h
  have hbad := (h 2 0 1 1 (by decide)).1
  omega

/-- Exchange zero-based labels `2` and `3` in a four-label model. -/
def swap23 (i : Fin 4) : Fin 4 := if i = 2 then 3 else if i = 3 then 2 else i

/-- The candidate source tuple `(b1, b1, b2, b1)`. -/
def sourceTuple {B : Type} (b1 b2 : B) (i : Fin 4) : B :=
  if i = 2 then b2 else b1

/-- The candidate target tuple `(b1, b1, b1, b2)`. -/
def targetTuple {B : Type} (b1 b2 : B) (i : Fin 4) : B :=
  if i = 3 then b2 else b1

/-- The explicit exchange transports the displayed tuple, moves the candidate
theta position `3` to `2`, and is its own inverse. This checks labels only;
it does not establish an admissible Ind1 action or Kummer membership. -/
theorem swap23_tuple_and_theta {B : Type} (b1 b2 : B) :
    (∀ i : Fin 4, sourceTuple b1 b2 (swap23 i) = targetTuple b1 b2 i) ∧
    swap23 3 = 2 ∧ (∀ i : Fin 4, swap23 (swap23 i) = i) := by
  constructor
  · intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi with h | h | h | h <;> subst i <;> rfl
  · constructor
    · rfl
    · decide

/-- The two candidate place labels; no local fields are asserted to exist. -/
inductive Place where
  | b1
  | b2
  deriving DecidableEq

/-- Candidate rho values depend on the place label, in units of `1/7`.
Their applicability to actual IUT local data is not established. -/
def rhoNumerator (b : Place) : Int := match b with
  | .b1 => 1
  | .b2 => 6

/-- Rho follows the place labels: source slots `2,3` have numerators `6,1`,
and target slots `2,3` have numerators `1,6`. The theta slot moves from source
`3` to target `2`, preserving its rho numerator `1`. Using the target last
slot `3` instead would use `6`, a difference of `5` in units of `1/7`.
This finite check establishes no actual Ind1 or Kummer membership. -/
theorem swap23_rho_positions :
    rhoNumerator (sourceTuple Place.b1 Place.b2 2) = 6 ∧
    rhoNumerator (sourceTuple Place.b1 Place.b2 3) = 1 ∧
    rhoNumerator (targetTuple Place.b1 Place.b2 2) = 1 ∧
    rhoNumerator (targetTuple Place.b1 Place.b2 3) = 6 ∧
    rhoNumerator (sourceTuple Place.b1 Place.b2 3) =
      rhoNumerator (targetTuple Place.b1 Place.b2 (swap23 3)) ∧
    rhoNumerator (targetTuple Place.b1 Place.b2 3) -
      rhoNumerator (targetTuple Place.b1 Place.b2 (swap23 3)) = 5 := by
  decide

end IUTAudit.LocalNumerics
