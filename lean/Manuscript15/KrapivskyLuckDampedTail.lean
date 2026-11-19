import Manuscript15.KrapivskyLuckLaplaceKernel
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! M15 §6.6, actual damped cosine integral and scaling of the surviving
Laplace kernel. These are steps toward the Tonelli/Si identity, not a
formalization of Binet's formula or the full energy identity. -/

open MeasureTheory Set Real Filter Topology
noncomputable section
namespace Manuscripts14And15.KrapivskyLuck

def tailPrimitive (s t : ℝ) : ℝ :=
  Real.exp (-s * t) * (s^2 * (Real.cos t - 1) - s * Real.sin t - 1) /
    (s^2 + 1)

theorem tailPrimitive_deriv (s t : ℝ) :
    HasDerivAt (tailPrimitive s)
      (s * Real.exp (-s * t) * (1 - Real.cos t)) t := by
  have he : HasDerivAt (fun x : ℝ => Real.exp (-s * x))
      (Real.exp (-s * t) * (-s)) t := by
    simpa using ((hasDerivAt_id t).const_mul (-s)).exp
  have hc := ((Real.hasDerivAt_cos t).sub_const (1 : ℝ)).const_mul (s^2)
  have hs := (Real.hasDerivAt_sin t).const_mul s
  have hp := (hc.sub hs).sub_const (1 : ℝ)
  unfold tailPrimitive
  convert (he.mul hp).div_const (s^2 + 1) using 1 <;> try rfl
  change s * Real.exp (-s*t) * (1-Real.cos t) =
    (Real.exp (-s*t) * (-s) * (s^2*(Real.cos t-1)-s*Real.sin t-1) +
      Real.exp (-s*t) * (s^2*(-Real.sin t)-s*Real.cos t)) / (s^2+1)
  field_simp [show s^2 + 1 ≠ 0 by positivity] <;> ring

theorem tailPrimitive_bound (s t : ℝ) (hs : 0 < s) :
    |tailPrimitive s t| ≤
      Real.exp (-s * t) * ((2*s^2+s+1)/(s^2+1)) := by
  have hd : 0 < s^2 + 1 := by positivity
  have hc₁ : 0 ≤ s^2 * (Real.cos t + 1) :=
    mul_nonneg (sq_nonneg s) (by linarith [Real.neg_one_le_cos t])
  have hc₂ : 0 ≤ s^2 * (1 - Real.cos t) :=
    mul_nonneg (sq_nonneg s) (by linarith [Real.cos_le_one t])
  have hs₁ : 0 ≤ s * (1 - Real.sin t) :=
    mul_nonneg hs.le (by linarith [Real.sin_le_one t])
  have hs₂ : 0 ≤ s * (Real.sin t + 1) :=
    mul_nonneg hs.le (by linarith [Real.neg_one_le_sin t])
  have hnum : |s^2*(Real.cos t-1)-s*Real.sin t-1| ≤ 2*s^2+s+1 := by
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg s]
  rw [tailPrimitive, abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos hd]
  calc
    _ ≤ Real.exp (-s*t) * (2*s^2+s+1) / (s^2+1) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnum (Real.exp_pos _).le) hd.le
    _ = _ := by ring

theorem tailPrimitive_tendsto (s : ℝ) (hs : 0 < s) :
    Tendsto (tailPrimitive s) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => -s*t) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp
      ((tendsto_id : Tendsto (fun t : ℝ => t) atTop atTop).const_mul_atTop hs)
    change Tendsto (fun t : ℝ => -(s*t)) atTop atBot at h
    simpa only [neg_mul] using h
  have he : Tendsto (fun t : ℝ => Real.exp (-s*t)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  have hb : Tendsto (fun t : ℝ => Real.exp (-s*t)*((2*s^2+s+1)/(s^2+1)))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using he.mul
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2*s^2+s+1)/(s^2+1)) atTop
        (𝓝 ((2*s^2+s+1)/(s^2+1))))
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq, sub_zero]
  exact squeeze_zero (fun t => abs_nonneg _) (fun t => tailPrimitive_bound s t hs) hb

/-- Actual improper integral; nonnegative derivative, no integrability hypothesis. -/
theorem damped_cosine_tail (s : ℝ) (hs : 0 < s) :
    (∫ t : ℝ in Ioi (2 * Real.pi),
       s * Real.exp (-s*t) * (1 - Real.cos t)) =
      Real.exp (-s*(2*Real.pi))/(s^2+1) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (a := 2 * Real.pi) (fun t _ => tailPrimitive_deriv s t)
    (fun t _ => mul_nonneg (mul_nonneg hs.le (Real.exp_pos _).le)
      (sub_nonneg.mpr (Real.cos_le_one t)))
    (tailPrimitive_tendsto s hs)
  rw [h]
  simp [tailPrimitive, Real.cos_two_pi, Real.sin_two_pi] <;> ring

/-- Exact substitution u=(2π)s in the actual m=1 kernel from #369. -/
theorem scaled_laplaceKernel_one :
    (∫ s : ℝ in Ioi 0, Real.exp (-(2*Real.pi)*s)/(s^2+1)) =
      Real.pi * laplaceKernel 1 := by
  let a : ℝ := 2*Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  let g : ℝ → ℝ := fun u => Real.exp (-u)/(u^2+a^2)
  have hg : (fun s : ℝ => Real.exp (-a*s)/(s^2+1)) =
      fun s => a^2 * g (a*s) := by
    funext s
    dsimp [g]
    rw [show -a*s = -(a*s) by ring]
    field_simp [ha.ne', show s^2+1 ≠ 0 by positivity,
      show (a*s)^2+a^2 ≠ 0 by positivity] <;> ring
  change (∫ s : ℝ in Ioi 0, Real.exp (-a*s)/(s^2+1)) = _
  rw [hg, integral_const_mul, integral_comp_mul_left_Ioi g 0 ha]
  simp only [mul_zero, smul_eq_mul]
  have hk : laplaceKernel 1 = 2 * ∫ u : ℝ in Ioi 0, g u := by
    simp only [laplaceKernel, Nat.one_ne_zero, if_false, laplaceIntegrand, Nat.cast_one,
      one_pow, mul_one]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    dsimp [g, a]
    ring_nf
  rw [hk]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  dsimp [a] at *
  field_simp [hpi] <;> ring

end Manuscripts14And15.KrapivskyLuck
#print axioms Manuscripts14And15.KrapivskyLuck.tailPrimitive_deriv
#print axioms Manuscripts14And15.KrapivskyLuck.tailPrimitive_bound
#print axioms Manuscripts14And15.KrapivskyLuck.tailPrimitive_tendsto
#print axioms Manuscripts14And15.KrapivskyLuck.damped_cosine_tail
#print axioms Manuscripts14And15.KrapivskyLuck.scaled_laplaceKernel_one
