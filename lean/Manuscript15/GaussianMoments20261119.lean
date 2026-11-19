import Manuscript15.InternalHyperlinks20261115
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! M15 §7.2, eq:central-slope-gaussian-moments.
Actual half-line Lebesgue integrals, including the positive scale parameter.
The uniform all-order asymptotic remainder is not asserted here. -/

open Real Set MeasureTheory
noncomputable section
namespace Manuscript15.GaussianMoment
open InternalHyperlinks20261115

def moment (r : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ (2*r+2) * Real.exp (-(x^2))

theorem moment_gamma (r : ℕ) :
    moment r = (1/2) * Real.Gamma ((r:ℝ)+3/2) := by
  have hn : (0:ℝ) ≤ ((2*r+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hq : (-1:ℝ) < ((2*r+2:ℕ):ℝ) := by linarith
  have h := integral_rpow_mul_exp_neg_rpow (p := (2:ℝ))
      (q := ((2*r+2:ℕ):ℝ)) (by norm_num) hq
  have ha : (((2*r+2:ℕ):ℝ)+1)/2 = (r:ℝ)+3/2 := by push_cast; ring
  simpa only [moment, Real.rpow_natCast, Real.rpow_two, ha] using h

theorem moment_pos (r : ℕ) : 0 < moment r := by
  rw [moment_gamma]
  positivity

theorem moment_ratio (r : ℕ) : moment r / moment 0 = gaussianWeight r := by
  simp only [moment_gamma, Nat.cast_zero, zero_add]
  rw [← gaussian_gamma_ratio r]
  have hn : Real.Gamma (3/2 : ℝ) ≠ 0 := by positivity
  field_simp [hn] <;> ring

theorem moment_ratio_binomial (r : ℕ) :
    moment r / moment 0 =
      ((2*r+1:ℕ):ℝ) * (r.factorial:ℝ) * ((2*r).choose r:ℝ) / 4^r := by
  rw [moment_ratio, gaussian_weight_central_binomial]

theorem moment_recurrence (r : ℕ) :
    moment (r+1) = ((2*(r:ℝ)+3)/2) * moment r := by
  have h : (r:ℝ)+3/2 ≠ 0 := by positivity
  rw [moment_gamma, moment_gamma, Nat.cast_succ,
    show (r:ℝ)+1+3/2 = ((r:ℝ)+3/2)+1 by ring, Real.Gamma_add_one h]
  ring

theorem moment_zero : moment 0 = Real.sqrt Real.pi / 4 := by
  simp only [moment_gamma, Nat.cast_zero, zero_add]
  rw [show (3/2:ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

theorem scaled_gaussian_moment (r : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in Ioi 0, x^(2*r+2) * Real.exp (-b*x^2)) =
      b ^ (-((r:ℝ)+3/2)) * moment r := by
  have hn : (0:ℝ) ≤ ((2*r+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hq : (-1:ℝ) < ((2*r+2:ℕ):ℝ) := by linarith
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := (2:ℝ))
      (q := ((2*r+2:ℕ):ℝ)) (b := b) (by norm_num) hq hb
  have ha : (((2*r+2:ℕ):ℝ)+1)/2 = (r:ℝ)+3/2 := by push_cast; ring
  have hn' : -(((2*r+2:ℕ):ℝ)+1)/2 = -((r:ℝ)+3/2) := by push_cast; ring
  simp only [Real.rpow_natCast, Real.rpow_two, ha, hn'] at h
  rw [moment_gamma, h]
  ring

end Manuscript15.GaussianMoment

#print axioms Manuscript15.GaussianMoment.moment_gamma
#print axioms Manuscript15.GaussianMoment.moment_pos
#print axioms Manuscript15.GaussianMoment.moment_ratio
#print axioms Manuscript15.GaussianMoment.moment_ratio_binomial
#print axioms Manuscript15.GaussianMoment.moment_recurrence
#print axioms Manuscript15.GaussianMoment.moment_zero
#print axioms Manuscript15.GaussianMoment.scaled_gaussian_moment
