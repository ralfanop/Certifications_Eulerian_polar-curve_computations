import Manuscript15.GeometryAnalysis20261126

/-! M15 hydraulic comparison: the exact parametrized arclength integral of
the three-cusp hypocycloid. Reuses the verified derivative and speed-square
identities. The identification with the perimeter of the enclosed domain
requires the separate geometric simple-curve argument. -/

open MeasureTheory Set
noncomputable section
namespace Manuscript15.DeltoidArclength20261127
open Manuscript15.GeometryAnalysis20261126

theorem abs_sin_integral_three_pi :
    (∫ t in (0:ℝ)..(3*Real.pi), |Real.sin t|) = 6 := by
  have hp := Real.pi_pos
  have h02 : (0:ℝ) ≤ Real.pi := hp.le
  have h12 : Real.pi ≤ 2*Real.pi := by linarith
  have h23 : 2*Real.pi ≤ 3*Real.pi := by linarith
  have h1 : (∫ t in (0:ℝ)..Real.pi, |Real.sin t|) = 2 := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi, Real.sin t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le h02] at ht
        exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi ht.1 ht.2)
      _ = _ := by rw [integral_sin, Real.cos_zero, Real.cos_pi] <;> norm_num
  have h2 : (∫ t in Real.pi..(2*Real.pi), |Real.sin t|) = 2 := by
    calc
      _ = ∫ t in Real.pi..(2*Real.pi), -Real.sin t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le h12] at ht
        have h : 0 ≤ Real.sin (t-Real.pi) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
        rw [Real.sin_sub, Real.cos_pi, Real.sin_pi] at h
        have hn : Real.sin t ≤ 0 := by linarith
        exact abs_of_nonpos hn
      _ = _ := by
        rw [intervalIntegral.integral_neg, integral_sin, Real.cos_pi, Real.cos_two_pi] <;> norm_num
  have hcos3 : Real.cos (3*Real.pi) = -1 := by
    rw [show 3*Real.pi = Real.pi+2*Real.pi by ring, Real.cos_add,
      Real.cos_pi, Real.cos_two_pi, Real.sin_pi, Real.sin_two_pi] <;> norm_num
  have h3 : (∫ t in (2*Real.pi)..(3*Real.pi), |Real.sin t|) = 2 := by
    calc
      _ = ∫ t in (2*Real.pi)..(3*Real.pi), Real.sin t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le h23] at ht
        have h : 0 ≤ Real.sin (t-2*Real.pi) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2])
        rw [Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi] at h
        have hn : 0 ≤ Real.sin t := by linarith
        exact abs_of_nonneg hn
      _ = _ := by rw [integral_sin, Real.cos_two_pi, hcos3] <;> norm_num
  have hc : Continuous (fun t : ℝ => |Real.sin t|) := Real.continuous_sin.abs
  have hi01 : IntervalIntegrable (fun t : ℝ => |Real.sin t|) volume 0 Real.pi :=
    hc.intervalIntegrable _ _
  have hi12 : IntervalIntegrable (fun t : ℝ => |Real.sin t|) volume Real.pi (2*Real.pi) :=
    hc.intervalIntegrable _ _
  have hi02 : IntervalIntegrable (fun t : ℝ => |Real.sin t|) volume 0 (2*Real.pi) :=
    hc.intervalIntegrable _ _
  have hi23 : IntervalIntegrable (fun t : ℝ => |Real.sin t|) volume (2*Real.pi) (3*Real.pi) :=
    hc.intervalIntegrable _ _
  have h01 := intervalIntegral.integral_add_adjacent_intervals hi01 hi12
  have h03 := intervalIntegral.integral_add_adjacent_intervals hi02 hi23
  linarith

theorem abs_sin_scaled_integral :
    (∫ t in (0:ℝ)..(2*Real.pi), |Real.sin ((3/2:ℝ)*t)|) = 4 := by
  have h := intervalIntegral.mul_integral_comp_mul_left
    (f := fun t : ℝ => |Real.sin t|) (a := (0:ℝ)) (b := 2*Real.pi) (3/2:ℝ)
  rw [mul_zero, show (3/2:ℝ)*(2*Real.pi) = 3*Real.pi by ring] at h
  rw [abs_sin_integral_three_pi] at h
  linarith

theorem deltoid_speed_abs (b t : ℝ) :
    Real.sqrt ((deriv (deltoidX b) t)^2+(deriv (deltoidY b) t)^2) =
      4*|b|*|Real.sin ((3/2:ℝ)*t)| := by
  rw [(deltoid_derivatives b t).1.deriv, (deltoid_derivatives b t).2.deriv,
    deltoid_speed_squared]
  have ht : 1-Real.cos (3*t) = 2*(Real.sin ((3/2:ℝ)*t))^2 := by
    rw [show 3*t = 2*((3/2:ℝ)*t) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq ((3/2:ℝ)*t)]
  rw [ht, show 8*b^2*(2*(Real.sin ((3/2:ℝ)*t))^2) =
    (4*b*Real.sin ((3/2:ℝ)*t))^2 by ring, Real.sqrt_sq_eq_abs,
    abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]

theorem deltoid_arclength (b : ℝ) :
    (∫ t in (0:ℝ)..(2*Real.pi),
      Real.sqrt ((deriv (deltoidX b) t)^2+(deriv (deltoidY b) t)^2)) = 16*|b| := by
  have he : (fun t : ℝ =>
      Real.sqrt ((deriv (deltoidX b) t)^2+(deriv (deltoidY b) t)^2)) =
      (fun t : ℝ => (4*|b|)*|Real.sin ((3/2:ℝ)*t)|) := by
    funext t
    exact deltoid_speed_abs b t
  rw [he, intervalIntegral.integral_const_mul, abs_sin_scaled_integral]
  ring

end Manuscript15.DeltoidArclength20261127

#print axioms Manuscript15.DeltoidArclength20261127.abs_sin_integral_three_pi
#print axioms Manuscript15.DeltoidArclength20261127.abs_sin_scaled_integral
#print axioms Manuscript15.DeltoidArclength20261127.deltoid_speed_abs
#print axioms Manuscript15.DeltoidArclength20261127.deltoid_arclength
