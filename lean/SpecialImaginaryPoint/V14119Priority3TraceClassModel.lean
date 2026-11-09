import Mathlib
import SpecialImaginaryPoint.Section67ScalarCertificate
import GegenbauerFock.RealComplexPositiveSpectralAutomaticTraceClassBridge
import GegenbauerFock.PositiveTraceDiagonalSpectralBridge

/-!
# Manuscript 14.119 — Priority 3: genuine Hilbert trace-class Dirichlet spectral inverse

This module constructs an ACTUAL bounded complex-linear operator on the
infinite-dimensional Hilbert space l²(ℕ, ℂ), not just an eigenvalue list.
It is the operator-norm sum of the positive rank-one projections weighted
by 1/(π²(n+1)²), the Dirichlet inverse spectral multipliers.

The concrete PDE domain identification with the second-derivative
Dirichlet operator on L²(0,1) is NOT claimed here. Neither the
Fredholm determinant nor zeta regularisation is defined by the scalar
Euler product; those are separate obligations of Priority 3.

The project-compatible complex CFC trace-class predicate used below
was ported and kernel-checked in V007, with basis independence proved
there. No new axioms or sorry are required.
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

/-- The actual positive bounded operator is in the full CFC-absolute
(source-compatible Physlib) trace class, not merely a spectral sequence. -/
theorem inverse_isTraceClass :
    ProbabilisticTheory.IsTraceClass inverse := by
  have hs : Summable (fun n : ℕ =>
      (inner ℂ (b n) (inverse (b n))).re) :=
    σ_summable.congr (fun n => (inverse_diagonal n).symm)
  exact GegenbauerFock.Ultraspherical.
    complex_nonneg_isTraceClass_of_summable_natBasis_diagonal
      inverse inverse_nonneg b hs

/-- The genuine CFC trace norm equals the sum of positive Dirichlet
inverse eigenvalues, independently of the trace-class witness basis. -/
theorem inverse_traceNorm_eq :
    ProbabilisticTheory.traceNorm inverse inverse_isTraceClass =
      ∑' n : ℕ, σ n := by
  rw [GegenbauerFock.HilbertSchmidtBasis.
    positiveTrace_traceNorm_eq_diagonal_tsum
      inverse inverse_isTraceClass inverse_nonneg b]
  exact tsum_congr inverse_diagonal

#print axioms Manuscript14Priority3.TraceClassModel.σ_summable
#print axioms Manuscript14Priority3.TraceClassModel.term_summable
#print axioms Manuscript14Priority3.TraceClassModel.inverse_eigen
#print axioms Manuscript14Priority3.TraceClassModel.inverse_nonneg
#print axioms Manuscript14Priority3.TraceClassModel.inverse_diagonal
#print axioms Manuscript14Priority3.TraceClassModel.inverse_isTraceClass
#print axioms Manuscript14Priority3.TraceClassModel.inverse_traceNorm_eq

end Manuscript14Priority3.TraceClassModel
