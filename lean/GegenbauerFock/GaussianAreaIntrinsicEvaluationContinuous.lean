import GegenbauerFock.GaussianAreaFullIntrinsicReproducing

/-!
# V007 — bounded point evaluation on the complete intrinsic Gaussian Fock space

Since the canonical analytic representative equals the bounded
Gaussian coefficient projection at every point, intrinsic entire
evaluation itself is a continuous complex-linear functional.

This does not assume that arbitrary ambient Gaussian L² classes have
pointwise values; the domain is the intrinsic entire submodule.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Point evaluation on the whole intrinsic Bargmann–Fock Hilbert space
is genuinely continuous in the Gaussian L² topology. -/
noncomputable def intrinsicEntireEvaluationContinuous
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    entireGaussianL2Submodule alpha →L[ℂ] ℂ :=
  { toLinearMap := intrinsicEntireEvaluation alpha ha z
    cont := by
      have hfun :
          (fun x : entireGaussianL2Submodule alpha =>
            intrinsicEntireEvaluation alpha ha z x) =
          (fun x : entireGaussianL2Submodule alpha =>
            projectedGaussianEvaluation alpha ha z
              (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
        funext x
        exact intrinsicEntireEvaluation_eq_projected_full alpha ha x z
      change Continuous (fun x : entireGaussianL2Submodule alpha =>
        intrinsicEntireEvaluation alpha ha z x)
      rw [hfun]
      exact (projectedGaussianEvaluation alpha ha z).continuous.comp
        continuous_subtype_val }

/-- The continuous evaluation functional agrees pointwise with the
canonical entire Gaussian L² representative. -/
theorem intrinsicEntireEvaluationContinuous_apply
    (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) (x : entireGaussianL2Submodule alpha) :
    intrinsicEntireEvaluationContinuous alpha ha z x =
      intrinsicEntireEvaluation alpha ha z x := rfl

#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluationContinuous_apply

end GegenbauerFock.GaussianArea
