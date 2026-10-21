import Candidates.OrbitQuotient
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum.Prime

set_option autoImplicit false
namespace OrbitQuotient.HullTool

def family {n m : ℕ} (perms : Fin m → Equiv.Perm (Fin n)) :
    Finset (Equiv.Perm (Fin n)) := Finset.univ.image perms

lemma family_nonempty {n m : ℕ} (perms : Fin m → Equiv.Perm (Fin n))
    (hm : 0 < m) : (family perms).Nonempty := by
  exact ⟨perms ⟨0, hm⟩, Finset.mem_image.mpr ⟨⟨0, hm⟩, Finset.mem_univ _, rfl⟩⟩

/-- Finite lower-bound and witness checks identify the existing hull exactly. -/
theorem checked_hull {n m : ℕ} (perms : Fin m → Equiv.Perm (Fin n))
    (hm : 0 < m) (k out : Fin n → ℕ)
    (lower : ∀ j i, out j ≤ k ((perms i).symm j))
    (attained : ∀ j, ∃ i, out j = k ((perms i).symm j)) :
    out = hullThresh (family perms) (family_nonempty perms hm) k := by
  have hh := hull_thresholds (family perms) (family_nonempty perms hm) k
  funext j
  apply Nat.le_antisymm
  · obtain ⟨γ, hγ, hval⟩ := hh.2 j
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hγ
    rw [hval]
    exact lower j i
  · obtain ⟨i, hi⟩ := attained j
    rw [hi]
    exact hh.1 j (perms i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)

end OrbitQuotient.HullTool
