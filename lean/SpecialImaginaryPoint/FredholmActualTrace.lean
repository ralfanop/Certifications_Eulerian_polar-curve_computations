import SharedCore.NuclearDiagonalTrace
import SpecialImaginaryPoint.V14119Priority3OptimalNuclearMass
import SpecialImaginaryPoint.V14119Priority3FredholmCompressionTraceFirstDerivative
import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# Genuine complex trace on the CFC trace ideal used by the determinant

The trace is defined independently of the determinant, by the absolutely
summable diagonal on the actual Hilbert basis of H = ℓ²(ℕ, ℂ). Optimal
nuclear representations supply the hypotheses of the basis-independent
diagonal trace theorem. The trace is a bounded complex-linear functional
of norm at most one for the genuine CFC trace norm.

Finally the actual finite-compression traces converge to this trace,
identifying it with the determinant's derivative at zero. The formula
at general resolvent points is a separate subsequent theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Manuscript14Priority3.ActualTrace

open Filter Topology InnerProductSpace
open scoped InnerProductSpace
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.NuclearRankOne
open SharedCore.NuclearDiagonalTrace
open Manuscript14Priority3.FiniteRankFredholm
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FredholmCompressionTraceFirstDerivative

/-- Absolute summability of the true diagonal on every Hilbert basis. -/
theorem diagonal_abs_summable (T : ProbabilisticTheory.TraceClass H)
    {ι : Type*} (c : HilbertBasis ι ℂ H) :
    Summable (fun i => ‖⟪c i, T.1 (c i)⟫_ℂ‖) := by
  obtain ⟨w, d, u, v, hcost, hsum⟩ := traceClass_nuclear_representation T
  have hop : (∑' i, rankOne ℂ (u i) (v i)) = T.1 := by
    rw [← nuclear_tsum_operator u v hcost, hsum]
  exact nuclear_diagonal_abs_summable c u v hcost T.1 hop

/-- Definition by the genuine Hilbert-basis diagonal, not by a determinant. -/
def actualTrace (T : ProbabilisticTheory.TraceClass H) : ℂ :=
  ∑' n, ⟪b n, T.1 (b n)⟫_ℂ

/-- The trace definition agrees with the diagonal sum in every Hilbert basis. -/
theorem actualTrace_eq_diagonal (T : ProbabilisticTheory.TraceClass H)
    {ι : Type*} (c : HilbertBasis ι ℂ H) :
    actualTrace T = ∑' i, ⟪c i, T.1 (c i)⟫_ℂ := by
  obtain ⟨w, d, u, v, hcost, hsum⟩ := traceClass_nuclear_representation T
  have hop : (∑' i, rankOne ℂ (u i) (v i)) = T.1 := by
    rw [← nuclear_tsum_operator u v hcost, hsum]
  exact nuclear_diagonal_basis_independent b c u v hcost T.1 hop

/-- Sharp trace-norm bound for arbitrary nonnormal CFC trace-class maps. -/
theorem actualTrace_norm_le (T : ProbabilisticTheory.TraceClass H) :
    ‖actualTrace T‖ ≤ ‖T‖ := by
  obtain ⟨w, d, u, v, hcost, hsum, hmass⟩ :=
    traceClass_exists_optimal_nuclear_representation T
  have hop : (∑' i, rankOne ℂ (u i) (v i)) = T.1 := by
    rw [← nuclear_tsum_operator u v hcost, hsum]
  exact (nuclear_diagonal_norm_le b u v hcost T.1 hop).trans hmass.le

theorem actualTrace_add (T S : ProbabilisticTheory.TraceClass H) :
    actualTrace (T + S) = actualTrace T + actualTrace S := by
  unfold actualTrace
  simp only [ProbabilisticTheory.TraceClass.add_operator,
    ContinuousLinearMap.add_apply, inner_add_right]
  exact ((diagonal_abs_summable T b).of_norm).tsum_add
    ((diagonal_abs_summable S b).of_norm)

theorem actualTrace_smul (a : ℂ) (T : ProbabilisticTheory.TraceClass H) :
    actualTrace (a • T) = a * actualTrace T := by
  unfold actualTrace
  simp only [ProbabilisticTheory.TraceClass.smul_operator,
    ContinuousLinearMap.smul_apply, inner_smul_right, tsum_mul_left]

/-- The actual trace as a continuous complex-linear functional on S₁. -/
def traceCLM : ProbabilisticTheory.TraceClass H →L[ℂ] ℂ :=
  ({ toFun := actualTrace
     map_add' := actualTrace_add
     map_smul' := fun a T => by simpa using actualTrace_smul a T } :
      ProbabilisticTheory.TraceClass H →ₗ[ℂ] ℂ).mkContinuous 1
    (fun T => by simpa using actualTrace_norm_le T)

theorem traceCLM_norm_le : ‖traceCLM‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro T
  change ‖actualTrace T‖ ≤ 1 * ‖T‖
  simpa only [one_mul] using actualTrace_norm_le T

/-- The genuine finite Hilbert-compression matrix traces converge to
the independently defined, basis-independent trace. -/
theorem compression_trace_tendsto (T : ProbabilisticTheory.TraceClass H) :
    Tendsto (fun N : ℕ => (compressedCFC N T).trace) atTop (𝓝 (actualTrace T)) := by
  unfold actualTrace
  have h := ((diagonal_abs_summable T b).of_norm).hasSum.tendsto_sum_nat
  convert h using 1
  funext N
  simp only [Matrix.trace, Matrix.diag, compressedCFC, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

/-- Actual determinant derivative = actual operator trace at zero. -/
theorem fredholm_deriv_zero_eq_actualTrace (T : ProbabilisticTheory.TraceClass H) :
    deriv (fredholmDet T) 0 = actualTrace T :=
  tendsto_nhds_unique
    (finiteFredholm_compression_trace_tendsto_universal_deriv_zero T)
    (compression_trace_tendsto T)

#print axioms diagonal_abs_summable
#print axioms actualTrace_eq_diagonal
#print axioms actualTrace_norm_le
#print axioms actualTrace_add
#print axioms actualTrace_smul
#print axioms traceCLM_norm_le
#print axioms compression_trace_tendsto
#print axioms fredholm_deriv_zero_eq_actualTrace

end Manuscript14Priority3.ActualTrace
