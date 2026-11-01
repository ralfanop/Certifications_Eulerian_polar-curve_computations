import GegenbauerFock.GaussianAreaTaylorUniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# V007 — mean-value property and circular submean bound for intrinsic entire Fock vectors

This is a genuinely analytic ingredient toward the missing full Gaussian
holomorphic polynomial-density theorem. The circle mean is an actual
interval integral, and the proof uses the complex Cauchy integral formula,
not any polynomial-density or onto assumption.

A separate step is still needed to integrate the circular submean
inequality radially against Gaussian area and control point evaluation
by the ambient L² norm. No such bound on the full intrinsic Fock
space is claimed here.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The Cauchy mean-value property for an arbitrary entire function,
formulated with Mathlib's actual normalized circle integral. -/
theorem entire_circleAverage_eq_value
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    Real.circleAverage f c R = f c := by
  have hcauchy :
      (∮ z in C(c, R), (z - c)⁻¹ • f z) =
        (2 * Real.pi * Complex.I : ℂ) • f c := by
    exact Complex.circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable
      hR Set.countable_empty hf.continuous.continuousOn
      (by
        intro z hz
        exact hf.differentiableAt)
  rw [Real.circleAverage_eq_circleIntegral hR.ne', hcauchy]
  rw [inv_smul_smul₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- Submean inequality for the modulus of an arbitrary entire function.
The right side is the genuine circular average, not a formal integral. -/
theorem entire_norm_le_circleAverage_norm
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    ‖f c‖ ≤ Real.circleAverage (fun z : ℂ => ‖f z‖) c R := by
  rw [← entire_circleAverage_eq_value f hf c R hR]
  exact Real.norm_circleAverage_le_circleAverage_norm

/-- The intrinsic entire Gaussian representative satisfies the same
mean-value formula, without assuming polynomial density. -/
theorem intrinsicEntire_circleAverage_eq_evaluation
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    Real.circleAverage (entireRepresentative alpha x) c R =
      intrinsicEntireEvaluation alpha ha c x := by
  exact entire_circleAverage_eq_value
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) c R hR

/-- Circular submean estimate for the independently defined intrinsic
Gaussian holomorphic space; no closure or onto theorem is assumed. -/
theorem intrinsicEntire_norm_le_circleAverage_norm
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha)
    (c : ℂ) (R : ℝ) (hR : 0 < R) :
    ‖intrinsicEntireEvaluation alpha ha c x‖ ≤
      Real.circleAverage
        (fun z : ℂ => ‖entireRepresentative alpha x z‖) c R := by
  exact entire_norm_le_circleAverage_norm
    (entireRepresentative alpha x)
    (entireRepresentative_differentiable alpha x) c R hR

#print axioms GegenbauerFock.GaussianArea.entire_circleAverage_eq_value
#print axioms GegenbauerFock.GaussianArea.entire_norm_le_circleAverage_norm
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_circleAverage_eq_evaluation
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_norm_le_circleAverage_norm

end GegenbauerFock.GaussianArea
