import Mathlib
import SpecialImaginaryPoint.SonineIntegralMoment

/-!
# Manuscript 14.1 §4 — genuine Sonine averaging on complex even polynomials

For `z : ℂ`, with integration variable `u : ℝ`, the actual averaging
transform is
  M f z = (1/2) ∫_{u=-1}¹ f (z * (sqrt (1-u²) : ℂ)) du.

This is NOT a formal coefficient surrogate: it is a Bochner integral with
complex values. The theorem identifies its action on complex even monomials
and all finite even complex Taylor polynomials. Global complex entire
functions remain a separate limiting/analytic question.
-/

namespace Manuscript14Sonine

open MeasureTheory intervalIntegral

noncomputable def sonineAverageComplex (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∫ u in (-1 : ℝ)..1,
    f (z * (Real.sqrt (1 - u ^ 2) : ℂ))

private theorem interval_nonneg (u : ℝ)
    (hu : u ∈ Set.uIcc (-1 : ℝ) 1) : 0 ≤ 1 - u ^ 2 := by
  rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hu
  rcases hu with ⟨hlo, hhi⟩
  have hp : 0 ≤ (1 - u) * (1 + u) := by
    exact mul_nonneg (by linarith) (by linarith)
  nlinarith

private theorem complex_even_power (n : ℕ) (z : ℂ) (u : ℝ)
    (hu : 0 ≤ 1 - u ^ 2) :
    (z * (Real.sqrt (1 - u ^ 2) : ℂ)) ^ (2*n) =
       z ^ (2*n) * ((1 - u ^ 2 : ℝ) ^ n : ℂ) := by
  calc
    (z * (Real.sqrt (1-u^2) : ℂ)) ^ (2*n) =
        ((z * (Real.sqrt (1-u^2) : ℂ)) ^ 2) ^ n := by rw [pow_mul]
    _ = (z ^ 2 * ((1-u^2 : ℝ) : ℂ)) ^ n := by
      rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hu]
    _ = z ^ (2*n) * ((1-u^2 : ℝ) ^ n : ℂ) := by
      rw [mul_pow, pow_mul, ← Complex.ofReal_pow]

theorem sonineAverageComplex_even_monomial (n : ℕ) (z : ℂ) :
    sonineAverageComplex (fun w : ℂ => w ^ (2*n)) z =
      (moment n : ℂ) * z ^ (2*n) := by
  unfold sonineAverageComplex
  have heq :
      (∫ u in (-1 : ℝ)..1,
        (z * (Real.sqrt (1-u^2) : ℂ)) ^ (2*n)) =
      ∫ u in (-1 : ℝ)..1,
        z ^ (2*n) * ((1-u^2 : ℝ)^n : ℂ) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact complex_even_power n z u (interval_nonneg u hu)
  rw [heq, intervalIntegral.integral_const_mul]
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal]
  let J : ℝ := ∫ u in (-1 : ℝ)..1, (1-u^2)^n
  have hm_real : (1 / 2 : ℝ) * J = (moment n : ℝ) := by
    simpa [J] using integral_monomial_sonine n
  have hm : (1 / 2 : ℂ) * (J : ℂ) = (moment n : ℂ) := by
    calc
      (1 / 2 : ℂ) * (J : ℂ) = (((1 / 2 : ℝ) * J) : ℂ) := by
        norm_num
      _ = ((moment n : ℝ) : ℂ) := by rw [hm_real]
      _ = (moment n : ℂ) := by norm_cast
  change (1 / 2 : ℂ) * (z^(2*n) * (J : ℂ)) =
    (moment n : ℂ) * z^(2*n)
  calc
    (1 / 2 : ℂ) * (z^(2*n) * (J : ℂ)) =
      ((1 / 2 : ℂ) * (J : ℂ)) * z^(2*n) := by ring
    _ = (moment n : ℂ) * z^(2*n) := by rw [hm]

def evenPolynomialComplex (s : Finset ℕ) (a : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ s, a n * z^(2*n)

theorem sonineAverageComplex_evenPolynomial (s : Finset ℕ)
    (a : ℕ → ℂ) (z : ℂ) :
    sonineAverageComplex (evenPolynomialComplex s a) z =
      ∑ n ∈ s, a n * (moment n : ℂ) * z^(2*n) := by
  have hsum :
      (∫ u in (-1 : ℝ)..1,
        ∑ n ∈ s, a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n)) =
      ∑ n ∈ s,
        ∫ u in (-1 : ℝ)..1,
          a n * (z * (Real.sqrt (1-u^2) : ℂ))^(2*n) := by
    apply intervalIntegral.integral_finsetSum
    intro n hn
    apply Continuous.intervalIntegrable
    fun_prop
  unfold sonineAverageComplex evenPolynomialComplex
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul]
  have h := sonineAverageComplex_even_monomial n z
  unfold sonineAverageComplex at h
  calc
    (1 / 2 : ℂ) *
      (a n * (∫ u in (-1 : ℝ)..1,
        (z * (Real.sqrt (1-u^2) : ℂ))^(2*n))) =
      a n * ((1 / 2 : ℂ) * (∫ u in (-1 : ℝ)..1,
        (z * (Real.sqrt (1-u^2) : ℂ))^(2*n))) := by ring
    _ = a n * ((moment n : ℂ) * z^(2*n)) := by rw [h]
    _ = a n * (moment n : ℂ) * z^(2*n) := by ring

#print axioms Manuscript14Sonine.sonineAverageComplex_even_monomial
#print axioms Manuscript14Sonine.sonineAverageComplex_evenPolynomial

end Manuscript14Sonine
