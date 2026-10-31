import GegenbauerFock.GaussianAreaEntireL2Submodule
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# V007 — uniqueness of entire Gaussian-L² representatives

The normalized Gaussian density is strictly positive at every complex
point. Consequently the weighted Gaussian measure and planar Lebesgue
measure have the same null sets, and the Gaussian measure is positive
on every nonempty open set.

Thus two continuous, in particular entire, representatives of the
same Gaussian-L² class coincide *everywhere*, not merely almost
everywhere. This is a prerequisite for intrinsic Fock evaluation.

This does NOT establish polynomial density or the onto Fock isometry.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Planar Lebesgue measure is absolutely continuous with respect
to the strictly positive weighted Gaussian measure for α > 0. -/
theorem volume_absolutelyContinuous_gaussianAreaMeasure
    (alpha : ℝ) (ha : 0 < alpha) :
    (volume : Measure ℂ) ≪ gaussianAreaMeasure alpha := by
  unfold gaussianAreaMeasure
  apply withDensity_absolutelyContinuous'
  · have hm : Measurable (fun z : ℂ =>
        ENNReal.ofReal ((alpha / Real.pi) *
          Real.exp (-alpha * ‖z‖ ^ 2))) := by
      fun_prop
    exact hm.aemeasurable
  · filter_upwards [] with z
    apply ENNReal.ofReal_ne_zero_iff.mpr
    have hcoef : 0 < alpha / Real.pi :=
      div_pos ha Real.pi_pos
    exact mul_pos hcoef (Real.exp_pos _)

/-- The genuine weighted Gaussian area measure has full support:
every nonempty open subset of ℂ has positive measure. -/
theorem gaussianAreaMeasure_isOpenPosMeasure
    (alpha : ℝ) (ha : 0 < alpha) :
    (gaussianAreaMeasure alpha).IsOpenPosMeasure :=
  (volume_absolutelyContinuous_gaussianAreaMeasure alpha ha).isOpenPosMeasure

/-- Equality Gaussian-a.e. of continuous functions forces
pointwise equality on the whole complex plane. -/
theorem continuous_eq_of_gaussian_ae_eq
    (alpha : ℝ) (ha : 0 < alpha)
    {f g : ℂ → ℂ}
    (h : f =ᵐ[gaussianAreaMeasure alpha] g)
    (hf : Continuous f) (hg : Continuous g) :
    f = g := by
  letI : (gaussianAreaMeasure alpha).IsOpenPosMeasure :=
    gaussianAreaMeasure_isOpenPosMeasure alpha ha
  exact Measure.eq_of_ae_eq h hf hg

/-- Two entire representatives of a Gaussian L² equivalence
class agree everywhere. -/
theorem entireGaussianRepresentative_unique
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
    {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hfx : f =ᵐ[gaussianAreaMeasure alpha] (x : ℂ → ℂ))
    (hgx : g =ᵐ[gaussianAreaMeasure alpha] (x : ℂ → ℂ)) :
    f = g :=
  continuous_eq_of_gaussian_ae_eq alpha ha
    (hfx.trans hgx.symm) hf.continuous hg.continuous

#print axioms GegenbauerFock.GaussianArea.volume_absolutelyContinuous_gaussianAreaMeasure
#print axioms GegenbauerFock.GaussianArea.gaussianAreaMeasure_isOpenPosMeasure
#print axioms GegenbauerFock.GaussianArea.continuous_eq_of_gaussian_ae_eq
#print axioms GegenbauerFock.GaussianArea.entireGaussianRepresentative_unique

end GegenbauerFock.GaussianArea
