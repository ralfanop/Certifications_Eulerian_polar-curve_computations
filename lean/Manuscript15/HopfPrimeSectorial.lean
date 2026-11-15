import Mathlib

noncomputable section

open Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius LSeries.notation

namespace Manuscript15.HopfPrimeSectorial

/-- The zero-indexed Möbius weight; the term at zero is zero. -/
def mobiusWeight (t : ℂ) (n : ℕ) : ℂ :=
  LSeries.term (↗μ) t n

theorem mobius_weight_summable (t : ℂ) (ht : 1 < t.re) :
    Summable (fun n => ‖mobiusWeight t n‖) := by
  have h : LSeriesSummable (↗μ) t := LSeriesSummable_moebius_iff.mpr ht
  change Summable (fun n => ‖LSeries.term (↗μ) t n‖)
  exact (show Summable (LSeries.term (↗μ) t) from h).norm

theorem tsum_mobius_weight (t : ℂ) (ht : 1 < t.re) :
    (∑' n, mobiusWeight t n) = 1 / riemannZeta t := by
  change LSeries (↗μ) t = 1 / riemannZeta t
  have h := LSeries_one_mul_Lseries_moebius ht
  rw [LSeries_one_eq_riemannZeta ht] at h
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re ht)).2
  simpa only [mul_comm] using h

/-- The dominated sectorial limiting step, conditional on pointwise convergence
and a uniform logarithmic-derivative bound along the chosen approach. -/
theorem sectorial_weighted_limit {α : Type*} {l : Filter α}
    (t : ℂ) (ht : 1 < t.re) (f : α → ℕ → ℂ) (c : ℂ) (C : ℝ)
    (hlim : ∀ n, Tendsto (fun x => f x n) l (𝓝 c))
    (hbound : ∀ᶠ x in l, ∀ n, ‖f x n‖ ≤ C) :
    Tendsto (fun x => ∑' n, mobiusWeight t n * f x n) l
      (𝓝 (c / riemannZeta t)) := by
  have H : Tendsto (fun x => ∑' n, mobiusWeight t n * f x n) l
      (𝓝 (∑' n, mobiusWeight t n * c)) :=
    tendsto_tsum_of_dominated_convergence
      ((mobius_weight_summable t ht).mul_right C)
      (fun n => tendsto_const_nhds.mul (hlim n))
      (hbound.mono fun x hx n => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hx n) (norm_nonneg _))
  rw [tsum_mul_right, tsum_mobius_weight t ht] at H
  simpa [div_eq_mul_inv, mul_comm] using H

theorem zeta_log_derivative_zero :
    deriv riemannZeta 0 / riemannZeta 0 =
      Complex.log (2 * (Real.pi : ℂ)) := by
  rw [deriv_riemannZeta_zero, riemannZeta_zero]
  ring

/-- The explicitly continued sectorial expression evaluated at the origin. -/
theorem continued_value_zero :
    (deriv riemannZeta 0 / riemannZeta 0) / riemannZeta 0 =
      -2 * Complex.log (2 * (Real.pi : ℂ)) := by
  rw [zeta_log_derivative_zero, riemannZeta_zero]
  ring

/-- Exponentiating the continued value gives the positive-real scalar in ℂ. -/
theorem prime_regularized_scalar :
    Complex.exp (-((deriv riemannZeta 0 / riemannZeta 0) / riemannZeta 0)) =
      (2 * (Real.pi : ℂ)) ^ 2 := by
  rw [continued_value_zero]
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  rw [show -(-2 * Complex.log (2 * (Real.pi : ℂ))) =
      Complex.log (2 * (Real.pi : ℂ)) + Complex.log (2 * (Real.pi : ℂ)) by ring,
    Complex.exp_add, Complex.exp_log hp, pow_two]

/-- For the unit round Hopf circle, its spectral zeta is 2 ζ(2s).
The following scalar calculation uses the derivative at zero of that expression. -/
theorem circle_determinant_scalar :
    Complex.exp (-4 * deriv riemannZeta 0) = (2 * (Real.pi : ℂ)) ^ 2 := by
  rw [deriv_riemannZeta_zero]
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  rw [show -4 * (-Complex.log (2 * (Real.pi : ℂ)) / 2) =
      Complex.log (2 * (Real.pi : ℂ)) + Complex.log (2 * (Real.pi : ℂ)) by ring,
    Complex.exp_add, Complex.exp_log hp, pow_two]

theorem prime_circle_scalar_agreement :
    Complex.exp (-((deriv riemannZeta 0 / riemannZeta 0) / riemannZeta 0)) =
      Complex.exp (-4 * deriv riemannZeta 0) := by
  rw [prime_regularized_scalar, circle_determinant_scalar]

/-- Coefficient identity with k=M-1, avoiding negative real exponents. -/
theorem terminal_hopf_coefficient (k : ℕ) :
    (1 : ℝ) / 2 / (2 * Real.pi) ^ (2 * k) =
      (1 : ℝ) / 2 / (4 * Real.pi ^ 2) ^ k := by
  rw [pow_mul, show (2 * Real.pi) ^ 2 = 4 * Real.pi ^ 2 by ring]

end Manuscript15.HopfPrimeSectorial

#print axioms Manuscript15.HopfPrimeSectorial.mobius_weight_summable
#print axioms Manuscript15.HopfPrimeSectorial.tsum_mobius_weight
#print axioms Manuscript15.HopfPrimeSectorial.sectorial_weighted_limit
#print axioms Manuscript15.HopfPrimeSectorial.zeta_log_derivative_zero
#print axioms Manuscript15.HopfPrimeSectorial.continued_value_zero
#print axioms Manuscript15.HopfPrimeSectorial.prime_regularized_scalar
#print axioms Manuscript15.HopfPrimeSectorial.circle_determinant_scalar
#print axioms Manuscript15.HopfPrimeSectorial.prime_circle_scalar_agreement
#print axioms Manuscript15.HopfPrimeSectorial.terminal_hopf_coefficient
