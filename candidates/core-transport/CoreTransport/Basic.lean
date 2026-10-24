import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace CoreTransport
open Filter Topology
noncomputable section

/-- The literal logarithm power series, not a conjugate definition. -/
def localLog {K : Type*} [Field K] [TopologicalSpace K] (x : K) : K :=
  ∑' n : ℕ, (-1 : K) ^ n * (x - 1) ^ (n + 1) / (n + 1)

theorem localLog_natural {K L : Type*} [Field K] [Field L]
    [TopologicalSpace K] [TopologicalSpace L] [T2Space L]
    (e : K ≃+* L) (he : Continuous e) (he' : Continuous e.symm) (x : K) :
    e (localLog x) = localLog (e x) := by
  unfold localLog
  rw [Function.LeftInverse.map_tsum _ he he' e.symm_apply_apply]
  simp only [map_div₀, map_mul, map_pow, map_neg, map_one, map_sub, map_add, map_natCast]

/-- This domain condition is proved from the same arrow's continuity in both directions. -/
theorem principal_unit_iff {K L : Type*} [NormedField K] [NormedField L]
    (e : K ≃+* L) (he : Continuous e) (he' : Continuous e.symm) (x : K) :
    ‖e x - 1‖ < 1 ↔ ‖x - 1‖ < 1 := by
  constructor
  · intro hx
    have h := (he'.tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hx)
    have hh : Tendsto (fun n : ℕ => (x - 1) ^ n) atTop (𝓝 0) := by
      simpa only [map_zero, map_pow, map_sub, map_one, e.symm_apply_apply, Function.comp_def] using h
    exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hh
  · intro hx
    have h := (he.tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mpr hx)
    have hh : Tendsto (fun n : ℕ => (e x - 1) ^ n) atTop (𝓝 0) := by
      simpa only [map_zero, map_pow, map_sub, map_one, Function.comp_def] using h
    exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.mp hh

end
end CoreTransport

namespace CoreTransport
noncomputable section

/-- The actual image of the principal-unit domain under the logarithm series. -/
def logImage (K : Type*) [NormedField K] : Set K :=
  localLog '' {u : K | ‖u - 1‖ < 1}

theorem logImage_transport {K L : Type*} [NormedField K] [NormedField L]
    (e : K ≃+* L) (he : Continuous e) (he' : Continuous e.symm) :
    e '' logImage K = logImage L := by
  ext y
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨e u, (principal_unit_iff e he he' u).mpr hu,
      (localLog_natural e he he' u).symm⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨localLog (e.symm u), ⟨e.symm u, ?_, rfl⟩, ?_⟩
    · exact (principal_unit_iff e.symm he' he u).mpr hu
    · simpa only [e.apply_symm_apply] using localLog_natural e he he' (e.symm u)

/-- The same ring arrow transports the multiplication action, without redefining it. -/
theorem multiplication_square {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (s z : K) : e (s * z) = e s * e z := e.map_mul s z

/-- An actual root-of-unity orbit; no arbitrary permutation is admitted. -/
def torsionOrbit {K : Type*} [Field K] (n : ℕ) (θ : K) : Set K :=
  {z | ∃ ζ : K, ζ ^ n = 1 ∧ z = ζ * θ}

theorem torsionOrbit_transport {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (n : ℕ) (θ : K) :
    e '' torsionOrbit n θ = torsionOrbit n (e θ) := by
  ext y
  constructor
  · rintro ⟨z, ⟨ζ, hζ, rfl⟩, rfl⟩
    exact ⟨e ζ, by rw [← map_pow, hζ, map_one], e.map_mul ζ θ⟩
  · rintro ⟨ζ, hζ, rfl⟩
    refine ⟨e.symm ζ * θ, ⟨e.symm ζ, ?_, rfl⟩, ?_⟩
    · rw [← map_pow, hζ, map_one]
    · simp only [map_mul, e.apply_symm_apply]

/-- A principal fractional-ideal region, with its actual coefficient subring retained. -/
def principalRegion {K : Type*} [Field K] (O : Subring K) (θ : K) : Set K :=
  {z | ∃ a : O, z = (a : K) * θ}

theorem principalRegion_transport {K L : Type*} [Field K] [Field L]
    (e : K ≃+* L) (O : Subring K) (O' : Subring L)
    (hO : ∀ x, e x ∈ O' ↔ x ∈ O) (θ : K) :
    e '' principalRegion O θ = principalRegion O' (e θ) := by
  ext y
  constructor
  · rintro ⟨z, ⟨a, rfl⟩, rfl⟩
    exact ⟨⟨e a, (hO a).mpr a.property⟩, e.map_mul a θ⟩
  · rintro ⟨a, rfl⟩
    have ha : e.symm (a : L) ∈ O := (hO _).mp (by simp only [e.apply_symm_apply]; exact a.property)
    refine ⟨e.symm (a : L) * θ, ⟨⟨_, ha⟩, rfl⟩, ?_⟩
    simp only [map_mul, e.apply_symm_apply]

end
end CoreTransport


