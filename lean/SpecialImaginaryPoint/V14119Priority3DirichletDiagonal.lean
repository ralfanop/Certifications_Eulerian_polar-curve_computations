import Mathlib
import SpecialImaginaryPoint.Section67ScalarCertificate

/-!
# Priority 3 — actual Dirichlet spectral inverse as a bounded l² operator

This module proves norm-summability of the rank-one operator series,
its eigenvalue action on the canonical basis, and Loewner positivity.
It makes NO claim yet of the differential Dirichlet operator on L²(0,1).
-/

noncomputable section

namespace Manuscript14Priority3.TraceClassModel
open Filter Topology InnerProductSpace
open scoped ComplexOrder

abbrev H : Type := ℓ²(ℕ, ℂ)

/-- The canonical complete orthonormal basis of complex square summable sequences. -/
def b : HilbertBasis ℕ ℂ H := default

/-- Exact Dirichlet inverse eigenvalues with n indexed from zero. -/
def σ (n : ℕ) : ℝ :=
  1 / (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2)

theorem σ_pos (n : ℕ) : 0 < σ n := by
  unfold σ
  positivity

theorem σ_summable : Summable σ := by
  simpa only [σ, one_div] using Manuscript14Section67.summable_base

/-- The actual complex Hilbert-space nuclear summands. -/
def term (n : ℕ) : H →L[ℂ] H :=
  (σ n : ℂ) • rankOne ℂ (b n) (b n)

theorem term_norm (n : ℕ) : ‖term n‖ = σ n := by
  rw [term, norm_smul, norm_rankOne, b.orthonormal.norm_eq_one,
    b.orthonormal.norm_eq_one]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (σ_pos n).le]

/-- The series of actual bounded rank-one operators converges in OPERATOR NORM. -/
theorem term_summable : Summable term := by
  apply Summable.of_norm
  exact σ_summable.congr (fun n => (term_norm n).symm)

/-- The genuine bounded Dirichlet inverse spectral MODEL on l²(ℕ,ℂ). -/
def inverse : H →L[ℂ] H := ∑' n : ℕ, term n

/-- Every canonical basis vector is a genuine eigenvector of the
infinite-dimensional bounded operator, not merely a formal label. -/
theorem inverse_eigen (n : ℕ) :
    inverse (b n) = (σ n : ℂ) • b n := by
  have hs := term_summable
  unfold inverse
  rw [hs.tsum_apply (b n)]
  rw [tsum_eq_single n]
  · simp [term, rankOne_apply, inner_self_eq_norm_sq_to_K,
      b.orthonormal.norm_eq_one n]
  · intro k hk
    simp [term, rankOne_apply, b.orthonormal.inner_eq_zero hk]

/-- Positivity of each actual nuclear summand. -/
theorem term_isPositive (n : ℕ) : (term n).IsPositive := by
  have hc : (0 : ℂ) ≤ (σ n : ℂ) := by
    exact_mod_cast (σ_pos n).le
  exact (InnerProductSpace.isPositive_rankOne_self (b n)).smul_of_nonneg hc

/-- Positive spectral inverse operator in the Hilbert Loewner order,
obtained from the closed positive cone and operator-norm convergence. -/
theorem inverse_nonneg : (0 : H →L[ℂ] H) ≤ inverse := by
  have hpart (N : ℕ) :
      (0 : H →L[ℂ] H) ≤ ∑ n ∈ Finset.range N, term n := by
    exact (ContinuousLinearMap.nonneg_iff_isPositive).2 <|
      ContinuousLinearMap.isPositive_sum (Finset.range N)
        (fun n _ => term_isPositive n)
  exact isClosed_Ici.mem_of_tendsto
    term_summable.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall hpart)

/-- Each positive diagonal entry is exactly its certified eigenvalue. -/
theorem inverse_diagonal (n : ℕ) :
    (inner ℂ (b n) (inverse (b n))).re = σ n := by
  rw [inverse_eigen n, inner_smul_right, inner_self_eq_norm_sq_to_K,
    b.orthonormal.norm_eq_one n]
  norm_num


#print axioms Manuscript14Priority3.TraceClassModel.σ_summable
#print axioms Manuscript14Priority3.TraceClassModel.term_summable
#print axioms Manuscript14Priority3.TraceClassModel.inverse_eigen
#print axioms Manuscript14Priority3.TraceClassModel.inverse_nonneg
#print axioms Manuscript14Priority3.TraceClassModel.inverse_diagonal

end Manuscript14Priority3.TraceClassModel
