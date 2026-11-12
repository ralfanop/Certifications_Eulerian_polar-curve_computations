import SpecialImaginaryPoint.V14119Priority3OperatorCompressionDiagonalTraceLimit
import SpecialImaginaryPoint.V14119Priority3TraceClassModel

/-!
# Priority 3 — Dirichlet inverse spectral-model Fredholm derivative equals its CFC trace norm

The genuine positive Dirichlet spectral inverse operator A⁻¹ on the
specific complex Hilbert model ℓ²(ℕ, ℂ) has certified trace class,
eigenvectors b_n and positive eigenvalues σ_n.

Here we identify the derivative at z=0 of the ACTUAL universal CFC-S₁
Fredholm determinant of this *specific* Hilbert operator with the
positive spectral trace ∑' σ_n, which equals its CFC trace norm.

This is stronger than an auxiliary scalar-product identity: the
determinant here is the genuine universal Hilbert-compression limit
for the true trace-class operator. It does NOT identify this spectral
operator with an L²(0,1) differential Dirichlet inverse, nor prove any
relative zeta-regularization identity. It does not assert that the
derivative equals the trace norm for arbitrary nonpositive operators.
-/

noncomputable section

namespace Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace

open Filter Topology Set InnerProductSpace
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.OperatorCompressionDiagonalTraceLimit
open Manuscript14Priority3.FredholmCompressionTraceFirstDerivative

/-- The *actual* CFC-S₁ element representing the positive bounded
Dirichlet inverse spectral model on complex ℓ². -/
def dirichletInverseS1 : ProbabilisticTheory.TraceClass H :=
  ProbabilisticTheory.TraceClass.ofOperator H inverse inverse_isTraceClass

/-- The N-dimensional true Hilbert-compression matrix trace of the
Dirichlet inverse equals the finite positive eigenvalue sum. -/
theorem dirichletInverseS1_finite_compression_trace_eq
    (N : ℕ) :
    (compressedCFC N dirichletInverseS1).trace =
      ∑ i : Fin N, (σ i.val : ℂ) := by
  rw [compression_trace_eq_finite_basis_diagonal_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  change inner ℂ (b i.val) (inverse (b i.val)) = (σ i.val : ℂ)
  rw [inverse_eigen, inner_smul_right]
  simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]

/-- The genuine Dirichlet inverse finite Hilbert-compression matrix
traces converge to the actual positive complex spectral trace. -/
theorem dirichletInverseS1_finite_trace_tendsto_tsum :
    Tendsto (fun N : ℕ => (compressedCFC N dirichletInverseS1).trace)
      atTop (𝓝 (∑' n : ℕ, (σ n : ℂ))) := by
  have hsum : Summable (fun n : ℕ => (σ n : ℂ)) :=
    (RCLike.summable_ofReal (𝕜 := ℂ)).mpr σ_summable
  have ht := hsum.hasSum.tendsto_sum_nat
  have hseq (N : ℕ) :
      (compressedCFC N dirichletInverseS1).trace =
        ∑ i ∈ Finset.range N, (σ i : ℂ) := by
    rw [dirichletInverseS1_finite_compression_trace_eq]
    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => (σ n : ℂ)) N
  simpa only [hseq] using ht

/-- The derivative of the true universal CFC-S₁ Fredholm determinant
of the positive Dirichlet inverse equals the convergent complex
spectral trace, not just a formal scalar expression. -/
theorem dirichletInverseS1_fredholm_deriv_zero_eq_spectral_tsum :
    deriv (fredholmDet dirichletInverseS1) 0 =
      ∑' n : ℕ, (σ n : ℂ) := by
  exact (tendsto_nhds_unique
    (finiteFredholm_compression_trace_tendsto_universal_deriv_zero dirichletInverseS1)
    dirichletInverseS1_finite_trace_tendsto_tsum)

/-- For the specific POSITIVE genuine Dirichlet inverse on ℓ²,
the derivative of the actual universal Fredholm determinant at 0
equals the CFC trace norm (embedded in ℂ). -/
theorem dirichletInverseS1_fredholm_deriv_zero_eq_traceNorm :
    deriv (fredholmDet dirichletInverseS1) 0 =
      (ProbabilisticTheory.traceNorm inverse inverse_isTraceClass : ℂ) := by
  rw [dirichletInverseS1_fredholm_deriv_zero_eq_spectral_tsum,
    inverse_traceNorm_eq]
  exact (RCLike.ofReal_tsum (𝕜 := ℂ) σ).symm

#print axioms Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace.dirichletInverseS1_finite_compression_trace_eq
#print axioms Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace.dirichletInverseS1_finite_trace_tendsto_tsum
#print axioms Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace.dirichletInverseS1_fredholm_deriv_zero_eq_spectral_tsum
#print axioms Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace.dirichletInverseS1_fredholm_deriv_zero_eq_traceNorm

end Manuscript14Priority3.DirichletInverseFredholmDerivativeTrace
