import GegenbauerFock.GaussianAreaEntirePolarFubini
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# V007 — exact polar-chart angular integral and normalized circle average

The complex polar chart uses (-π,π), whereas Mathlib's circleAverage
uses (0,2π). The following identity is unconditional and includes
the precise factor 2π. No holomorphic density theorem is assumed.
-/

noncomputable section

open Complex MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The polar angular integral on (-π,π) equals 2π times the
normalized circle average on the same geometric circle. -/
theorem polar_angular_integral_eq_two_pi_circleAverage
    (f : ℂ → ℂ) (r : ℝ) :
    (∫ theta in Set.Ioo (-Real.pi) Real.pi,
      f (Complex.polarCoord.symm (r, theta))) =
      (2 * Real.pi) • Real.circleAverage f 0 r := by
  have hmap (theta : ℝ) :
      Complex.polarCoord.symm (r, theta) =
        circleMap 0 r theta := by
    rw [Complex.polarCoord_symm_apply]
    simp [circleMap, Complex.exp_ofReal_mul_I]
  have hinterval :
      (∫ theta in Set.Ioo (-Real.pi) Real.pi,
        f (circleMap 0 r theta)) =
      (∫ theta in (-Real.pi)..Real.pi,
        f (circleMap 0 r theta)) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [integral_Ioc_eq_integral_Ioo]
  have hshift :
      (∫ theta in (-Real.pi)..Real.pi,
        f (circleMap 0 r theta)) =
      (∫ theta in (0 : ℝ)..2 * Real.pi,
        f (circleMap 0 r (theta + (-Real.pi)))) := by
    convert (intervalIntegral.integral_comp_add_right
      (f := fun theta : ℝ => f (circleMap 0 r theta))
      (a := 0) (b := 2 * Real.pi) (-Real.pi)).symm using 1 <;> ring
  have haverage :=
    Real.circleAverage_eq_integral_add
      (f := f) (c := (0 : ℂ)) (R := r) (-Real.pi)
  rw [hshift] at hinterval
  simp_rw [hmap]
  rw [hinterval, haverage]
  field_simp [Real.pi_ne_zero] <;> ring

#print axioms GegenbauerFock.GaussianArea.polar_angular_integral_eq_two_pi_circleAverage

end GegenbauerFock.GaussianArea
