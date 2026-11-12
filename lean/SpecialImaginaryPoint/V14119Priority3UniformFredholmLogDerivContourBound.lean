import SpecialImaginaryPoint.V14119Priority3UniformFredholmContourGap
import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLogDerivative
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Priority 3 — bounded genuine Fredholm logarithmic derivative on admissible contours

Let f_T(z) = det_F(I+zT) be the ACTUAL universal CFC Schatten-S₁
Hilbert-compression-limit Fredholm determinant of an arbitrary complex
trace-class Hilbert operator T. On each circle of admissible radius r,
f_T never vanishes; compactness yields a positive lower bound δ for
|f_T|. The complex derivative f_T' is entire and hence bounded by
some M on the same compact circle.

This proves an explicit finite contour bound
  ‖logDeriv f_T(z)‖ = ‖f_T'(z)/f_T(z)‖ ≤ M/δ.
It is a structural input for forthcoming argument-principle integrals.
The proof does NOT assert any contour integral formula or trace-resolvent
identity, nor assume normality or positivity of the operator.
-/

noncomputable section

namespace Manuscript14Priority3.UniformFredholmLogDerivContourBound

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmLogDerivative
open Manuscript14Priority3.AdmissibleContourRadii
open Manuscript14Priority3.UniformFredholmContourGap

/-- A globally finite norm bound for the TRUE universal Fredholm
logarithmic derivative along each admissible spectral circle.
The bound M/δ comes from compactness and continuous holomorphy,
and is independent of the angle of the contour point. -/
theorem universalFredholm_logDeriv_uniform_circle_bound
    (T : ProbabilisticTheory.TraceClass H) (r : ℝ)
    (hr : r ∈ (universalFredholmZeroRadiusSet T)ᶜ) :
    ∃ (δ M : ℝ), 0 < δ ∧ 0 ≤ M ∧
      ∀ z : ℂ, ‖z‖ = r →
        ‖logDeriv (fredholmDet T) z‖ ≤ M / δ := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    universalFredholm_exists_positive_uniform_circle_gap T r hr
  have hderivCont :
      ContinuousOn (deriv (fredholmDet T))
        (Metric.sphere (0 : ℂ) r) :=
    (universalFredholmDet_deriv_entire T).continuous.continuousOn
  obtain ⟨M, hM⟩ :=
    (isCompact_sphere (0 : ℂ) r).exists_bound_of_continuousOn'
      (f := deriv (fredholmDet T)) hderivCont
  refine ⟨δ, max M 0, hδpos, le_max_right _ _, ?_⟩
  intro z hz
  have hzCircle : z ∈ Metric.sphere (0 : ℂ) r := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  have hderiv :
      ‖deriv (fredholmDet T) z‖ ≤ max M 0 :=
    (hM z hzCircle).trans (le_max_left _ _)
  have hden : δ ≤ ‖fredholmDet T z‖ := hδ z hz
  have hdenpos : 0 < ‖fredholmDet T z‖ :=
    hδpos.trans_le hden
  calc
    ‖logDeriv (fredholmDet T) z‖ =
        ‖deriv (fredholmDet T) z‖ / ‖fredholmDet T z‖ := by
      simp only [logDeriv_apply, norm_div]
    _ ≤ (max M 0) / ‖fredholmDet T z‖ :=
      div_le_div_of_nonneg_right hderiv hdenpos.le
    _ ≤ (max M 0) / δ :=
      div_le_div_of_nonneg_left (le_max_right _ _) hδpos hden

#print axioms Manuscript14Priority3.UniformFredholmLogDerivContourBound.universalFredholm_logDeriv_uniform_circle_bound

end Manuscript14Priority3.UniformFredholmLogDerivContourBound
