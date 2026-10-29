import GegenbauerFock.GaussianAreaIntrinsicEvaluationContinuous
import GegenbauerFock.GaussianAreaFullIntrinsicEvaluation
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# V007 — quantitative norm bound for intrinsic Fock point evaluation

The entire-representative Gaussian L² space carries actual continuous
complex-linear point evaluations. Their operator norms are controlled
by coherent evaluation on the coefficient Hilbert space, so no
finite-polynomial or unbounded-functional assumption is required.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The operator norm of evaluation at z on the complete intrinsic
Gaussian Bargmann–Fock space is at most the corresponding coherent
evaluation norm on square-summable Taylor coefficients. -/
theorem intrinsicEntireEvaluationContinuous_norm_le
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖intrinsicEntireEvaluationContinuous alpha ha z‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
    (intrinsicEntireEvaluationContinuous alpha ha z)
    (norm_nonneg _)
  intro x
  change ‖intrinsicEntireEvaluation alpha ha z x‖ ≤
    ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖
  exact intrinsicEntireEvaluation_norm_le_full alpha ha x z

/-- Quantitative bounded evaluation for the canonical entire
representative in the genuine Gaussian L² norm. -/
theorem entireRepresentative_norm_le_coherentEvaluation
    (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) (x : entireGaussianL2Submodule alpha) :
    ‖entireRepresentative alpha x z‖ ≤
      ‖intrinsicEntireEvaluationContinuous alpha ha z‖ * ‖x‖ := by
  change ‖intrinsicEntireEvaluationContinuous alpha ha z x‖ ≤
      ‖intrinsicEntireEvaluationContinuous alpha ha z‖ * ‖x‖
  exact (intrinsicEntireEvaluationContinuous alpha ha z).le_opNorm x

#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous_norm_le
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_norm_le_coherentEvaluation

end GegenbauerFock.GaussianArea
