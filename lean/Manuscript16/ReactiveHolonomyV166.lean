import Mathlib

/-!
# M16 revision 16.6 §§14.4–14.5
Authoritative ZIP SHA256 ed3877cbb2250598bda640ca05ddb69194f4b0675db165cc7dcc94fd71796cc3.
Exact scalar TE identities, actual Lebesgue half-line integrals, and
closed-form holonomy identities. No operator-domain, spectral-product
limit, or full Maxwell realisation is asserted by these lemmas.
-/
open MeasureTheory Set

namespace Manuscript16.ReactiveHolonomy

theorem te_robin_coefficient (X omega mu : ℝ)
    (hX : X ≠ 0) (ho : omega ≠ 0) (hm : mu ≠ 0) :
    X * ((omega * mu / X) / (omega * mu)) = 1 := by
  field_simp [hX, ho, hm]

theorem te_magnetic_excess (eps mu omega beta kappa A : ℝ)
    (ho : omega ≠ 0) (hm : mu ≠ 0)
    (hd : kappa ^ 2 = omega ^ 2 * eps * mu + beta ^ 2) :
    mu * ((beta ^ 2 + kappa ^ 2) * A / (omega * mu)^2) / 4 -
      eps * A / 4 = beta ^ 2 * A / (2 * omega ^ 2 * mu) := by
  rw [hd]
  field_simp [ho, hm]
  <;> ring

/-- Genuine scalar Lebesgue integral of the squared exponential profile. -/
theorem te_decay_integral (beta : ℝ) (hb : 0 < beta) :
    (∫ z : ℝ in Ioi 0, Real.exp (-(2 * beta * z))) = 1 / (2 * beta) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1) (r := 2 * beta) (by norm_num) (by positivity)
  simpa only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one,
    Real.Gamma_one, mul_one] using h

/-- The imaginary normal flux coefficient equals the actual integrated
magnetic excess, with squared boundary amplitude A. -/
theorem te_integrated_flux (omega mu beta A : ℝ)
    (ho : omega ≠ 0) (hm : mu ≠ 0) (hb : 0 < beta) :
    -beta * A / (2 * omega * mu) =
      -2 * omega * (∫ z : ℝ in Ioi 0,
        (beta ^ 2 * A / (2 * omega ^ 2 * mu)) * Real.exp (-(2 * beta * z))) := by
  rw [integral_const_mul, te_decay_integral beta hb]
  field_simp [ho, hm, hb.ne']
  <;> ring

/-- The actual first evanescent moment of one positive spectral value. -/
theorem evanescent_scalar_moment (b : ℝ) (hb : 0 < b) :
    (∫ z : ℝ in Ioi 0, z * Real.exp (-(2 * Real.sqrt b * z))) = 1 / (4 * b) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 2) (r := 2 * Real.sqrt b) (by norm_num) (by positivity)
  have hG : Real.Gamma (2 : ℝ) = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two,
    hG, mul_one] at h
  rw [h, div_pow, mul_pow, Real.sq_sqrt hb.le]
  <;> norm_num

/-- Pairing the n and -n factors before taking an infinite product. -/
theorem paired_holonomy_numerator (n phi a : ℝ) :
    ((n-phi)^2+a^2) * ((-n-phi)^2+a^2) - (n^2+a^2)^2 =
      2 * phi^2 * (a^2-n^2) + phi^4 := by ring

noncomputable def momentClosed (a x c : ℝ) : ℝ :=
  (Real.pi / (4*a)) * Real.sinh (2*x) / (Real.cosh (2*x)-c)

noncomputable def productClosed (x c : ℝ) : ℝ :=
  (Real.cosh (2*x)-c) / (Real.cosh (2*x)-1)

noncomputable def hyperbolicProfile (x : ℝ) : ℝ := Real.sinh x / x

private theorem sinh_positive (x : ℝ) (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have h : Real.exp (-x) < Real.exp x := Real.exp_lt_exp.mpr (by linarith)
  linarith

theorem holonomy_denominators (x : ℝ) :
    Real.cosh (2*x)-1 = 2*(Real.sinh x)^2 ∧
    Real.cosh (2*x)+1 = 2*(Real.cosh x)^2 := by
  rw [Real.cosh_two_mul]
  constructor <;> linarith [Real.cosh_sq_sub_sinh_sq x]

theorem half_phase_cos : Real.cos (2 * Real.pi * (1/2 : ℝ)) = -1 := by
  rw [show 2 * Real.pi * (1/2 : ℝ) = Real.pi by ring, Real.cos_pi]

/-- Closed scalar moment ratio, not the spectral identification of the moments. -/
theorem half_moment_ratio (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    momentClosed a x (-1) / momentClosed a x 1 = (Real.tanh x)^2 := by
  obtain ⟨hm,hp⟩ := holonomy_denominators x
  have hs := sinh_positive x hx
  have hc := Real.cosh_pos x
  unfold momentClosed
  rw [sub_neg_eq_add, hp, hm, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp [ha.ne', hs.ne', hc.ne', Real.pi_ne_zero]
  <;> ring

theorem half_product_reciprocal (x : ℝ) (hx : 0 < x) :
    1 / productClosed x (-1) = (Real.tanh x)^2 := by
  obtain ⟨hm,hp⟩ := holonomy_denominators x
  unfold productClosed
  rw [sub_neg_eq_add, hp, hm, Real.tanh_eq_sinh_div_cosh]
  field_simp [(sinh_positive x hx).ne', (Real.cosh_pos x).ne']
  <;> ring

theorem half_eulerian_profile (x : ℝ) (hx : 0 < x) :
    x^2 * (hyperbolicProfile x)^4 / (hyperbolicProfile (2*x))^2 =
      (Real.tanh x)^2 := by
  unfold hyperbolicProfile
  rw [Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
  field_simp [hx.ne', (sinh_positive x hx).ne', (Real.cosh_pos x).ne']
  <;> ring

theorem half_ratio_strict (x : ℝ) (hx : 0 < x) :
    0 < (Real.tanh x)^2 ∧ (Real.tanh x)^2 < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hs := sinh_positive x hx
  have hc := Real.cosh_pos x
  have hlt := Real.sinh_lt_cosh x
  have hp : 0 < Real.sinh x / Real.cosh x := div_pos hs hc
  have hq : Real.sinh x / Real.cosh x < 1 := (div_lt_one hc).2 hlt
  constructor
  · positivity
  · nlinarith [mul_pos hp (sub_pos.mpr hq)]

end Manuscript16.ReactiveHolonomy

#print axioms Manuscript16.ReactiveHolonomy.te_robin_coefficient
#print axioms Manuscript16.ReactiveHolonomy.te_magnetic_excess
#print axioms Manuscript16.ReactiveHolonomy.te_decay_integral
#print axioms Manuscript16.ReactiveHolonomy.te_integrated_flux
#print axioms Manuscript16.ReactiveHolonomy.evanescent_scalar_moment
#print axioms Manuscript16.ReactiveHolonomy.paired_holonomy_numerator
#print axioms Manuscript16.ReactiveHolonomy.holonomy_denominators
#print axioms Manuscript16.ReactiveHolonomy.half_phase_cos
#print axioms Manuscript16.ReactiveHolonomy.half_moment_ratio
#print axioms Manuscript16.ReactiveHolonomy.half_product_reciprocal
#print axioms Manuscript16.ReactiveHolonomy.half_eulerian_profile
#print axioms Manuscript16.ReactiveHolonomy.half_ratio_strict
