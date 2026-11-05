import Mathlib
import SpecialImaginaryPoint.SonineIntegralMoment

/-!
# Manuscript 14.1, §4: Sonine integral averaging on even polynomials

The integrand here uses precisely the actual real Sonine map
  (Mf)(t) = (1/2)∫_{-1}¹ f(t*sqrt(1-u²)) du.
No formal substitute for sqrt is used in the definition.

The following statements give the exact averaging formula for every even
monomial and for all finite real-coefficient even polynomials.
For even entire functions, local uniform convergence and termwise
differentiation remain additional obligations.
-/

namespace Manuscript14Sonine

open MeasureTheory intervalIntegral

noncomputable def sonineAverageReal (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∫ u in (-1 : ℝ)..1,
    f (t * Real.sqrt (1 - u ^ 2))

private theorem sqrt_even_power (n : ℕ) (t u : ℝ)
    (hu : 0 ≤ 1 - u ^ 2) :
    (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n) =
      t ^ (2 * n) * (1 - u ^ 2) ^ n := by
  calc
    (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n) =
        ((t * Real.sqrt (1 - u ^ 2)) ^ 2) ^ n := by
          rw [pow_mul]
    _ = (t ^ 2 * (1 - u ^ 2)) ^ n := by
          rw [mul_pow, Real.sq_sqrt hu]
    _ = t ^ (2 * n) * (1 - u ^ 2) ^ n := by
          rw [mul_pow, pow_mul]

private theorem one_sub_sq_nonneg_on_interval (u : ℝ)
    (hu : u ∈ Set.uIcc (-1 : ℝ) 1) : 0 ≤ 1 - u ^ 2 := by
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  rcases hu with ⟨hlo, hhi⟩
  have hp : 0 ≤ (1 - u) * (1 + u) := by
    exact mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- The genuine integral transform sends t^(2n) to c_n t^(2n). -/
theorem sonineAverageReal_even_monomial (n : ℕ) (t : ℝ) :
    sonineAverageReal (fun s : ℝ => s ^ (2 * n)) t =
      (moment n : ℝ) * t ^ (2 * n) := by
  unfold sonineAverageReal
  have hcongr :
      (∫ u in (-1 : ℝ)..1,
          (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n)) =
        ∫ u in (-1 : ℝ)..1, t ^ (2 * n) * (1 - u ^ 2) ^ n := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact sqrt_even_power n t u (one_sub_sq_nonneg_on_interval u hu)
  rw [hcongr, intervalIntegral.integral_const_mul]
  calc
    (1 / 2 : ℝ) * (t ^ (2 * n) *
        (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n)) =
        ((1 / 2 : ℝ) * (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ n)) *
          t ^ (2 * n) := by ring
    _ = (moment n : ℝ) * t ^ (2 * n) := by
      rw [integral_monomial_sonine]

/-- Finite real-coefficient even Taylor polynomial. -/
def evenPolynomial (s : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ s, a n * t ^ (2 * n)

/-- The actual Sonine integral operator acts diagonally on every even polynomial. -/
theorem sonineAverageReal_evenPolynomial (s : Finset ℕ)
    (a : ℕ → ℝ) (t : ℝ) :
    sonineAverageReal (evenPolynomial s a) t =
      ∑ n ∈ s, a n * (moment n : ℝ) * t ^ (2 * n) := by
  have hsum :
      (∫ u in (-1 : ℝ)..1,
        ∑ n ∈ s, a n * (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n)) =
      ∑ n ∈ s,
        ∫ u in (-1 : ℝ)..1,
          a n * (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n) := by
    apply intervalIntegral.integral_finsetSum
    intro n hn
    apply Continuous.intervalIntegrable
    fun_prop
  unfold sonineAverageReal evenPolynomial
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul]
  have h := sonineAverageReal_even_monomial n t
  unfold sonineAverageReal at h
  calc
    (1 / 2 : ℝ) *
      (a n * (∫ u in (-1 : ℝ)..1,
        (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n))) =
      a n * ((1 / 2 : ℝ) * (∫ u in (-1 : ℝ)..1,
        (t * Real.sqrt (1 - u ^ 2)) ^ (2 * n))) := by ring
    _ = a n * ((moment n : ℝ) * t ^ (2 * n)) := by rw [h]
    _ = a n * (moment n : ℝ) * t ^ (2 * n) := by ring

#print axioms Manuscript14Sonine.sonineAverageReal_even_monomial
#print axioms Manuscript14Sonine.sonineAverageReal_evenPolynomial

end Manuscript14Sonine
