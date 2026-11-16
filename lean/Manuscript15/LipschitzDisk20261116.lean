import Mathlib

/-! M15 §8.1, Figure 2: sharp disk norm and scalar derivative bound.
The branch derivative formula for H₀ and the complex segment integration
theorem remain independent analytic obligations. -/
namespace Manuscript15.LipschitzDisk20261116

theorem disk_quadratic_bound (u v : ℝ)
    (h : u^2 + (v-1)^2 ≤ 1/4) :
    5/4 + 2*(v-1/2)^2 ≤ 1-u^2+v^2 := by
  nlinarith

theorem disk_complex_bound (z : ℂ)
    (h : z.re^2 + (z.im-1)^2 ≤ 1/4) :
    (5:ℝ)/4 ≤ ‖1-z^2‖ := by
  have hq := disk_quadratic_bound z.re z.im h
  have hr : (1-z^2).re = 1-z.re^2+z.im^2 := by
    simp [pow_two, Complex.mul_re]
    <;> ring
  have hn := Complex.abs_re_le_norm (1-z^2)
  rw [hr] at hn
  exact (show (5:ℝ)/4 ≤ 1-z.re^2+z.im^2 by
    nlinarith [sq_nonneg (z.im-1/2)]).trans ((le_abs_self _).trans hn)

theorem boundary_norm : ‖(1:ℂ)-(Complex.I/2)^2‖ = (5:ℝ)/4 := by
  have h : (1:ℂ)-(Complex.I/2)^2 = ((5/4:ℝ):ℂ) := by
    rw [div_pow, Complex.I_sq]
    push_cast
    ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem reciprocal_sqrt_bound (z : ℂ)
    (h : z.re^2 + (z.im-1)^2 ≤ 1/4) :
    1 / Real.sqrt ‖1-z^2‖ ≤ 2 / Real.sqrt 5 := by
  have hn := disk_complex_bound z h
  have h5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h5sq := Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)
  have hs := Real.sq_sqrt (norm_nonneg (1-z^2))
  have hp : 0 < Real.sqrt ‖1-z^2‖ := Real.sqrt_pos.2 (by linarith)
  apply (div_le_div_iff₀ hp h5).2
  nlinarith [sq_nonneg (2*Real.sqrt ‖1-z^2‖-Real.sqrt 5),
             mul_pos hp h5]

theorem modular_pair_product (s : ℂ) (hs : s ≠ 0) :
    (Complex.I/s)*(Complex.I*s) = -1 := by
  calc
    _ = Complex.I * Complex.I := by field_simp [hs]
    _ = -1 := by rw [← pow_two, Complex.I_sq]

theorem catalan_scalar_resolvent (x t : ℝ) (h : 1-x*t ≠ 0) :
    x*t/(1-x*t)^2 + 2*x^2*t^2/(1-x*t)^3 =
      x*t*(1+x*t)/(1-x*t)^3 := by
  field_simp [h]
  <;> ring

end Manuscript15.LipschitzDisk20261116

#print axioms Manuscript15.LipschitzDisk20261116.disk_quadratic_bound
#print axioms Manuscript15.LipschitzDisk20261116.disk_complex_bound
#print axioms Manuscript15.LipschitzDisk20261116.boundary_norm
#print axioms Manuscript15.LipschitzDisk20261116.reciprocal_sqrt_bound
#print axioms Manuscript15.LipschitzDisk20261116.modular_pair_product
#print axioms Manuscript15.LipschitzDisk20261116.catalan_scalar_resolvent
