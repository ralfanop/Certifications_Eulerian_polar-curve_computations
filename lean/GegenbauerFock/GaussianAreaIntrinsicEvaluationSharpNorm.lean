import GegenbauerFock.GaussianAreaIntrinsicEvaluationOperatorNorm
import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GaussianAreaIntrinsicPointwiseExpansion
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# V007 — exact norm of evaluation on the full intrinsic Bargmann–Fock space

The intrinsic Gaussian entire L² space is genuinely unitarily equivalent
to the ℓ² coefficient Hilbert space. The point-evaluation functional
on this true analytic subspace is a pullback of coherent ℓ² evaluation
through the unitary coefficient isometry. Therefore its norm is not
merely bounded above: it is exactly the coherent kernel norm.

In particular, the previously certified sharp exponential pointwise
estimate has the optimal constant, with no assumption of polynomial
density or surjectivity added as a premise.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Intrinsic entire evaluation on a synthesized Gaussian L² vector
is literally the coherent coefficient-space point evaluation. -/
theorem intrinsicEntireEvaluationContinuous_synthesis
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    intrinsicEntireEvaluationContinuous alpha ha z
        (coefficientSynthesisToIntrinsicEntire alpha ha a) =
      FockEvaluation.evaluation alpha ha z a := by
  have h :
      ((coefficientSynthesisToIntrinsicEntire alpha ha a :
        entireGaussianL2Submodule alpha) :
        Lp ℂ 2 (gaussianAreaMeasure alpha)) =
      coefficientSynthesisL2 alpha ha a := rfl
  rw [intrinsicEntireEvaluationContinuous_eq_coherent_analysis
      alpha ha (coefficientSynthesisToIntrinsicEntire alpha ha a) z,
    h, coefficientAnalysisL2_synthesis]

/-- The full intrinsic Fock evaluation norm is EXACTLY the coherent
ℓ² evaluation norm, and not only upper-bounded by that norm. -/
theorem intrinsicEntireEvaluationContinuous_norm_eq
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖intrinsicEntireEvaluationContinuous alpha ha z‖ =
      ‖FockEvaluation.evaluation alpha ha z‖ := by
  apply le_antisymm
  · exact intrinsicEntireEvaluationContinuous_norm_le alpha ha z
  · apply ContinuousLinearMap.opNorm_le_bound
      (FockEvaluation.evaluation alpha ha z)
      (norm_nonneg _)
    intro a
    calc
      ‖FockEvaluation.evaluation alpha ha z a‖ =
        ‖intrinsicEntireEvaluationContinuous alpha ha z
          (coefficientSynthesisToIntrinsicEntire alpha ha a)‖ := by
            rw [intrinsicEntireEvaluationContinuous_synthesis]
      _ ≤ ‖intrinsicEntireEvaluationContinuous alpha ha z‖ *
          ‖coefficientSynthesisToIntrinsicEntire alpha ha a‖ :=
        (intrinsicEntireEvaluationContinuous alpha ha z).le_opNorm _
      _ = ‖intrinsicEntireEvaluationContinuous alpha ha z‖ * ‖a‖ := by
        rw [(coefficientSynthesisToIntrinsicEntire alpha ha).norm_map]

/-- Exact squared operator norm of every point-evaluation functional
on the complete intrinsic holomorphic Gaussian L² Hilbert space. -/
theorem intrinsicEntireEvaluationContinuous_norm_sq
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖intrinsicEntireEvaluationContinuous alpha ha z‖ ^ 2 =
      Real.exp (alpha * ‖z‖ ^ 2) := by
  rw [intrinsicEntireEvaluationContinuous_norm_eq,
    FockEvaluation.evaluation_norm_sq]

#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous_synthesis
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous_norm_eq
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous_norm_sq

end GegenbauerFock.GaussianArea
