import Mathlib
import Manuscript17.StrongCycleJordan20261128

noncomputable section
namespace Manuscript17.OriginalJordanChains

open Matrix Polynomial Module.End
open Manuscript17.StrongCycleOriginal Manuscript17.StrongCycleChebyshev
open Manuscript17.StrongCycleJordan

/-- The recurrence is now on the original, not transposed, matrix. -/
theorem original_row (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ)
    (v : Fin (n+2) → ℂ) (i : Fin (n+1)) :
    (original n a r w *ᵥ v) i.castSucc =
      a i.castSucc * v i.castSucc + r * v i.succ := by
  classical
  have hi : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
  have hlast : i.castSucc.val ≠ n+1 := by omega
  unfold Matrix.mulVec dotProduct
  calc
    (∑ j, original n a r w i.castSucc j * v j) =
      ∑ j : Fin (n+2), ((if j = i.castSucc then a i.castSucc * v j else 0) +
        (if j = i.succ then r * v j else 0)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h0 : j = i.castSucc
      · subst j
        simp [original,hi]
      · by_cases h1 : j = i.succ
        · subst j
          simp [original,h0,Ne.symm h0]
        · have hs : i.castSucc.val+1 ≠ j.val := by
            intro he
            apply h1
            apply Fin.ext
            simpa using he.symm
          simp [original,h0,Ne.symm h0,h1,hlast,hs]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

theorem zero_initial_coordinate (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ)
    (hr : r ≠ 0) (v : Fin (n+2) → ℂ)
    (he : original n a r w *ᵥ v = z • v) (h0 : v 0 = 0) : v = 0 := by
  have hrec : ∀ i : Fin (n+1),
      r * v i.succ = (z-a i.castSucc) * v i.castSucc := by
    intro i
    have h := congrFun he i.castSucc
    rw [original_row] at h
    change a i.castSucc * v i.castSucc + r*v i.succ = z*v i.castSucc at h
    linear_combination h
  exact Manuscript17.StrongCycle.recurrence_unique n (fun i => z-a i) r hr v h0 hrec

def firstCoord (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ) :
    (Module.End.eigenspace (original n a r w).mulVecLin z) →ₗ[ℂ] ℂ where
  toFun v := v.val 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem firstCoord_injective (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ)
    (hr : r ≠ 0) : Function.Injective (firstCoord n a r w z) := by
  intro x y h
  have hz : firstCoord n a r w z (x-y) = 0 := by rw [map_sub,h,sub_self]
  have he := Module.End.mem_eigenspace_iff.mp (x-y).property
  change original n a r w *ᵥ ((x-y : Module.End.eigenspace (original n a r w).mulVecLin z) : Fin (n+2) → ℂ) =
    z • ((x-y : Module.End.eigenspace (original n a r w).mulVecLin z) : Fin (n+2) → ℂ) at he
  have hv := zero_initial_coordinate n a r w z hr _ he hz
  exact sub_eq_zero.mp (Subtype.ext hv)

theorem original_geometric_le_one (n : ℕ) (w z : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (A n w).mulVecLin z) ≤ 1 := by
  simpa [A] using LinearMap.finrank_le_finrank_of_injective
    (firstCoord_injective n (alpha n) (radius n) w z (radius_ne_zero n))

/-- A generalized eigenvector not in the eigenspace produces an actual
length-two Jordan chain, by choosing the least vanishing power. -/
theorem chain_of_generalized_not_eigen {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : Module.End ℂ V) (z : ℂ) (v : V)
    (hv : v ∈ Module.End.maxGenEigenspace f z)
    (hne : v ∉ Module.End.eigenspace f z) :
    ∃ x y : V, x ≠ 0 ∧ f x = z • x ∧ f y = z • y + x := by
  let D := f-z • (1 : Module.End ℂ V)
  have hnil : ∃ k : ℕ, (D^k) v = 0 := Module.End.mem_maxGenEigenspace.mp hv
  have hmin : (D^(Nat.find hnil)) v = 0 := Nat.find_spec hnil
  have hnot : D v ≠ 0 := by
    intro h
    apply hne
    rw [Module.End.mem_eigenspace_iff]
    simpa [D,sub_eq_zero] using h
  have hk : 2 ≤ Nat.find hnil := by
    by_contra! h
    have hcases : Nat.find hnil = 0 ∨ Nat.find hnil = 1 := by omega
    rcases hcases with h0 | h1
    · rw [h0,pow_zero] at hmin
      have hv0 : v = 0 := hmin
      exact hnot (by simp [hv0])
    · rw [h1,pow_one] at hmin
      exact hnot hmin
  let k := Nat.find hnil - 2
  have he : Nat.find hnil = k+2 := by dsimp [k]; omega
  let y := (D^k) v
  let x := D y
  have hx : x ≠ 0 := by
    intro hx0
    have hx1 : (D^(k+1)) v = 0 := by
      rw [pow_succ']
      exact hx0
    exact (Nat.not_lt_of_ge (Nat.find_min' hnil hx1)) (by omega)
  have hDx : D x = 0 := by
    have h := hmin
    rw [he,pow_succ',pow_succ'] at h
    exact h
  refine ⟨x,y,hx,?_,?_⟩
  · simpa [D,sub_eq_zero] using hDx
  · have hh : f y-z • y = x := by rfl
    exact sub_eq_iff_eq_add'.mp hh

theorem double_root_chain (n : ℕ) (w z : ℂ)
    (hm : rootMultiplicity z (A n w).charpoly = 2) :
    ∃ x y : Fin (n+2) → ℂ, x ≠ 0 ∧
      (A n w).mulVecLin x = z • x ∧
      (A n w).mulVecLin y = z • y + x := by
  let f := (A n w).mulVecLin
  have hdim : Module.finrank ℂ (Module.End.maxGenEigenspace f z) = 2 :=
    (generalized_dimension n w z).trans hm
  have hle := original_geometric_le_one n w z
  have hnot : ¬ Module.End.maxGenEigenspace f z ≤ Module.End.eigenspace f z := by
    intro h
    have hh := Submodule.finrank_mono h
    change Module.finrank ℂ (Module.End.eigenspace f z) ≤ 1 at hle
    omega
  obtain ⟨v,hv,hne⟩ := Set.not_subset.mp hnot
  exact chain_of_generalized_not_eigen f z v hv hne

#print axioms original_row
#print axioms zero_initial_coordinate
#print axioms firstCoord_injective
#print axioms original_geometric_le_one
#print axioms chain_of_generalized_not_eigen
#print axioms double_root_chain
end Manuscript17.OriginalJordanChains
