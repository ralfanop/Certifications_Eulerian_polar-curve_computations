import GegenbauerFock.GaussianAreaPolarRadialCircleBridge
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# V007 — scalar extraction from genuine Gaussian circular integrals

The whole circle-average argument is pointwise for each radius.
This module isolates scalar algebra, so the remaining moment–Taylor
proof may use the certified radial Gamma integral directly.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Two nested real scalar multiples may be taken through the
normalized complex-valued circle average at the same radius. -/
theorem circleAverage_nested_real_smul
    (f : ℂ → ℂ) (r a : ℝ) :
    Real.circleAverage
      (fun z : ℂ => r • (a • f z)) 0 r =
      (((r * a : ℝ) : ℂ)) * Real.circleAverage f 0 r := by
  have hf :
      (fun z : ℂ => r • (a • f z)) =
      (fun z : ℂ => (((r * a : ℝ) : ℂ)) * f z) := by
    funext z
    simp only [Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [hf]
  simpa only [smul_eq_mul] using
    (Real.circleAverage_fun_smul
      (a := ((r * a : ℝ) : ℂ))
      (f := f) (c := (0 : ℂ)) (R := r))

/-- The exact normalized Gaussian factor cancels the 2π from the
angular chart, leaving 2α times r exp(-αr²) pointwise in the
outer radial integration. -/
theorem gaussian_circleAverage_scalar_normalization
    (alpha r : ℝ) (f : ℂ → ℂ) :
    (2 * Real.pi) •
      Real.circleAverage
        (fun z : ℂ =>
          r • (((alpha / Real.pi) * Real.exp (-alpha * r ^ 2) : ℝ) • f z))
        0 r =
      ((2 * alpha : ℝ) : ℂ) *
        (((r * Real.exp (-alpha * r ^ 2) : ℝ) : ℂ) *
          Real.circleAverage f 0 r) := by
  rw [circleAverage_nested_real_smul]
  simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_div]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hpi]

#print axioms GegenbauerFock.GaussianArea.circleAverage_nested_real_smul
#print axioms GegenbauerFock.GaussianArea.gaussian_circleAverage_scalar_normalization

end GegenbauerFock.GaussianArea
