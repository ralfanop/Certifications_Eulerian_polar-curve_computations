import Mathlib
import Manuscript17.StrongCycleMinpoly20261127

noncomputable section
namespace Manuscript17.StrongCycleOriginal

open Matrix Polynomial Module.End
open Manuscript17.StrongCycleKrylov Manuscript17.StrongCycleMinpoly

/-! Lemma lem:Mn-cyclic in Cyclohedral.tex uses the transpose of M_n,
not a relabelling of its diagonal. This module transfers the certified
Krylov result to the original superdiagonal matrix. -/
def original (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℂ :=
  fun i j => if i = j then a i else
    if i.val+1 = j.val then r else
    if i.val = n+1 ∧ j.val = 0 then r*w else 0

theorem original_transpose (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) :
    (original n a r w).transpose = matrix n a r w := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [original,matrix]
  · have h' : j ≠ i := Ne.symm h
    simp [original,matrix,h,h',eq_comm,and_comm]

theorem original_powers_independent (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ)
    (hr : r ≠ 0) :
    LinearIndependent ℂ (fun j : Fin (n+2) => (original n a r w)^j.val) := by
  apply LinearIndependent.of_comp
    (Matrix.transposeLinearEquiv (Fin (n+2)) (Fin (n+2)) ℂ ℂ).toLinearMap
  change LinearIndependent ℂ (fun j : Fin (n+2) => ((original n a r w)^j.val).transpose)
  simp_rw [Matrix.transpose_pow, original_transpose]
  exact powers_independent n a r w hr

theorem original_minpoly_eq_charpoly (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ)
    (hr : r ≠ 0) :
    minpoly ℂ (original n a r w) = (original n a r w).charpoly := by
  apply minpoly.eq_of_linearIndependent ℂ (original n a r w)
    (Matrix.charpoly_monic _) (Matrix.aeval_self_charpoly _) (n+2)
  · simp [Matrix.charpoly_degree_eq_dim]
  · exact original_powers_independent n a r w hr

/-- The coordinate functional on the eigenspace of the transpose. -/
def lastCoord (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ) :
    (Module.End.eigenspace (matrix n a r w).mulVecLin z) →ₗ[ℂ] ℂ where
  toFun v := v.val (Fin.last (n+1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lastCoord_injective (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ)
    (hr : r ≠ 0) : Function.Injective (lastCoord n a r w z) := by
  intro x y h
  have hzero : lastCoord n a r w z (x-y) = 0 := by rw [map_sub,h,sub_self]
  have hv : ((x-y : Module.End.eigenspace (matrix n a r w).mulVecLin z) : Fin (n+2) → ℂ) = 0 := by
    by_contra hn
    have he := Module.End.mem_eigenspace_iff.mp (x-y).property
    change (matrix n a r w) *ᵥ ((x-y : Module.End.eigenspace (matrix n a r w).mulVecLin z) : Fin (n+2) → ℂ) =
      z • ((x-y : Module.End.eigenspace (matrix n a r w).mulVecLin z) : Fin (n+2) → ℂ) at he
    exact (eigenvector_last_nonzero n a r w z hr _ hn he) hzero
  have hsub : x-y = 0 := Subtype.ext hv
  exact sub_eq_zero.mp hsub

/-- Geometric multiplicity is at most one, including repeated roots. -/
theorem eigenspace_finrank_le_one (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ)
    (hr : r ≠ 0) : Module.finrank ℂ (Module.End.eigenspace (matrix n a r w).mulVecLin z) ≤ 1 := by
  simpa using LinearMap.finrank_le_finrank_of_injective (lastCoord_injective n a r w z hr)

#print axioms original_transpose
#print axioms original_powers_independent
#print axioms original_minpoly_eq_charpoly
#print axioms lastCoord_injective
#print axioms eigenspace_finrank_le_one

end Manuscript17.StrongCycleOriginal
