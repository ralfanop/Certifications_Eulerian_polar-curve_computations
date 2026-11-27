import Mathlib
import Manuscript17.StrongCycleKrylov20261127

noncomputable section
namespace Manuscript17.StrongCycleMinpoly

open Matrix Polynomial
open Manuscript17.StrongCycleKrylov

theorem iterate_eq_pow (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) (k : ℕ) :
    iterate n a r w k = (matrix n a r w)^k *ᵥ seed n := by
  induction k with
  | zero => simp [iterate]
  | succ k ih => rw [iterate, ih, pow_succ', Matrix.mulVec_mulVec]

theorem krylov_span (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) (hr : r ≠ 0) :
    Submodule.span ℂ (Set.range (fun j : Fin (n+2) => iterate n a r w j.val)) = ⊤ := by
  apply (krylov_linearIndependent n a r w hr).span_eq_top_of_card_eq_finrank
  simp

def evalSeed (n : ℕ) :
    Matrix (Fin (n+2)) (Fin (n+2)) ℂ →ₗ[ℂ] (Fin (n+2) → ℂ) where
  toFun A := A *ᵥ seed n
  map_add' A B := by rw [Matrix.add_mulVec]
  map_smul' c A := by rw [Matrix.smul_mulVec]; rfl

theorem powers_independent (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) (hr : r ≠ 0) :
    LinearIndependent ℂ (fun j : Fin (n+2) => (matrix n a r w)^j.val) := by
  apply LinearIndependent.of_comp (evalSeed n)
  change LinearIndependent ℂ (fun j : Fin (n+2) => (matrix n a r w)^j.val *ᵥ seed n)
  simp_rw [← iterate_eq_pow]
  exact krylov_linearIndependent n a r w hr

theorem minpoly_eq_charpoly (n : ℕ) (a : Fin (n+2) → ℂ) (r w : ℂ) (hr : r ≠ 0) :
    minpoly ℂ (matrix n a r w) = (matrix n a r w).charpoly := by
  apply minpoly.eq_of_linearIndependent ℂ (matrix n a r w) (matrix n a r w).charpoly_monic
    (Matrix.aeval_self_charpoly _) (n+2)
  · simp [Matrix.charpoly_degree_eq_dim]
  · exact powers_independent n a r w hr

/-- Zero last coordinate forces a reverse-ordered eigenvector to vanish. -/
theorem eigenvector_last_nonzero (n : ℕ) (a : Fin (n+2) → ℂ) (r w z : ℂ)
    (hr : r ≠ 0) (v : Fin (n+2) → ℂ) (hv : v ≠ 0)
    (he : (matrix n a r w) *ᵥ v = z • v) : v (Fin.last (n+1)) ≠ 0 := by
  intro hz
  apply hv
  funext j
  have haux : ∀ k : ℕ, ∀ hk : k ≤ n+1,
      v ⟨n+1-k, by omega⟩ = 0 := by
    intro k
    induction k with
    | zero => intro hk; exact hz
    | succ k ih =>
      intro hk
      have hk' : k ≤ n+1 := by omega
      let i : Fin (n+1) := ⟨n-k, by omega⟩
      have h1 : v i.succ = 0 := by
        convert ih hk' using 1
        congr 1
        apply Fin.ext
        simp [i]
        omega
      have hrow := congrFun he i.succ
      rw [row_succ, h1] at hrow
      simp [h1] at hrow
      have h0 : v i.castSucc = 0 := (mul_eq_zero.mp hrow).resolve_left hr
      convert h0 using 1
      congr 1
      apply Fin.ext
      simp [i]
      omega
  convert haux (n+1-j.val) (by omega) using 1
  congr 1
  apply Fin.ext
  simp
  omega

#print axioms iterate_eq_pow
#print axioms krylov_span
#print axioms powers_independent
#print axioms minpoly_eq_charpoly
#print axioms eigenvector_last_nonzero

end Manuscript17.StrongCycleMinpoly
