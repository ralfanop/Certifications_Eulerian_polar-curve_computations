import Mathlib
import SpecialImaginaryPoint.SonineBesselGlobal

/-!
# Manuscript 14.1 §4 — unconditional convergence of cylindrical Bessel Taylor series

We remove the pointwise absolute-summability hypotheses from the actual
Sonine integral / classical sinh and sin identities. The comparison is
with the absolutely convergent real exponential series at
r = ‖z‖² / 4. These theorems assert summability for every complex z.

The final unconditional conclusions identify the *genuine* Sonine
averaging integrals of the series-defined I0 and J0 functions with
Complex.sinh(z)/z and Complex.sin(z)/z for z ≠ 0.
-/

namespace Manuscript14Sonine

private theorem modifiedBesselCoefficient_pos (n : ℕ) :
    0 < modifiedBesselCoefficient n := by
  unfold modifiedBesselCoefficient
  positivity

private theorem bessel_summability_bound (z : ℂ) (n : ℕ) :
    ‖(modifiedBesselCoefficient n : ℂ) * z^(2*n)‖ ≤
      (‖z‖^2 / 4)^n / (Nat.factorial n : ℝ) := by
  let d : ℝ := (Nat.factorial n : ℝ)
  have hd : 1 ≤ d := by
    dsimp [d]
    exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hdpos : 0 < d := by linarith
  have hsq : d ≤ d^2 := by nlinarith
  have hcoef_pos : (0 : ℝ) ≤ (modifiedBesselCoefficient n : ℝ) := by
    exact_mod_cast (le_of_lt (modifiedBesselCoefficient_pos n))
  have hnorm :
      ‖(modifiedBesselCoefficient n : ℂ) * z^(2*n)‖ =
        (modifiedBesselCoefficient n : ℝ) * ‖z‖^(2*n) := by
    simp [norm_mul, norm_pow, Complex.norm_ratCast,
      abs_of_nonneg hcoef_pos]
  have hcoef :
      (modifiedBesselCoefficient n : ℝ) =
        1 / ((4 : ℝ)^n * d^2) := by
    simp [modifiedBesselCoefficient, d]
  have hreal :
      (modifiedBesselCoefficient n : ℝ) * ‖z‖^(2*n) =
        (‖z‖^2/4)^n / d^2 := by
    rw [hcoef]
    rw [div_pow, pow_mul]
    ring
  rw [hnorm, hreal]
  have hr : 0 ≤ (‖z‖^2/4)^n := by positivity
  have hineq :
      (‖z‖^2/4)^n * d ≤ (‖z‖^2/4)^n * d^2 :=
    mul_le_mul_of_nonneg_left hsq hr
  exact (div_le_div_iff₀ (by positivity : 0 < d^2) hdpos).2 hineq

/-- Universal absolute convergence of the power series defining I0. -/
theorem modifiedBesselSeries_abs_summable (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖(modifiedBesselCoefficient n : ℂ) * z^(2*n)‖) := by
  exact Summable.of_nonneg_of_le
    (fun n => norm_nonneg _)
    (bessel_summability_bound z)
    (Real.summable_pow_div_factorial (‖z‖^2/4))

/-- The alternating J0 coefficient sequence has the same absolute norms. -/
theorem ordinaryBesselSeries_abs_summable (z : ℂ) :
    Summable (fun n : ℕ =>
      ‖(ordinaryBesselCoefficient n : ℂ) * z^(2*n)‖) := by
  have hnorm (n : ℕ) :
      ‖(ordinaryBesselCoefficient n : ℂ) * z^(2*n)‖ =
        ‖(modifiedBesselCoefficient n : ℂ) * z^(2*n)‖ := by
    simp [ordinaryBesselCoefficient, norm_mul, norm_pow]
  simpa only [hnorm] using modifiedBesselSeries_abs_summable z

/-- The actual, not merely formal, modified-Bessel Sonine integral. -/
theorem sonine_modifiedBessel_integral_unconditional (z : ℂ) :
    z * sonineAverageComplex modifiedBesselSeries z = Complex.sinh z :=
  sonine_modifiedBessel_integral_mul z (modifiedBesselSeries_abs_summable z)

/-- The actual, not merely formal, ordinary-Bessel Sonine integral. -/
theorem sonine_ordinaryBessel_integral_unconditional (z : ℂ) :
    z * sonineAverageComplex ordinaryBesselSeries z = Complex.sin z :=
  sonine_ordinaryBessel_integral_mul z (ordinaryBesselSeries_abs_summable z)

theorem sonine_modifiedBessel_integral_eq_sinh_div (z : ℂ) (hz : z ≠ 0) :
    sonineAverageComplex modifiedBesselSeries z = Complex.sinh z / z := by
  apply (eq_div_iff hz).2
  simpa only [mul_comm] using sonine_modifiedBessel_integral_unconditional z

theorem sonine_ordinaryBessel_integral_eq_sin_div (z : ℂ) (hz : z ≠ 0) :
    sonineAverageComplex ordinaryBesselSeries z = Complex.sin z / z := by
  apply (eq_div_iff hz).2
  simpa only [mul_comm] using sonine_ordinaryBessel_integral_unconditional z

#print axioms Manuscript14Sonine.modifiedBesselSeries_abs_summable
#print axioms Manuscript14Sonine.ordinaryBesselSeries_abs_summable
#print axioms Manuscript14Sonine.sonine_modifiedBessel_integral_unconditional
#print axioms Manuscript14Sonine.sonine_ordinaryBessel_integral_unconditional
#print axioms Manuscript14Sonine.sonine_modifiedBessel_integral_eq_sinh_div
#print axioms Manuscript14Sonine.sonine_ordinaryBessel_integral_eq_sin_div

end Manuscript14Sonine
