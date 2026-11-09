import SpecialImaginaryPoint.V14119Asymptotic177Numerator

/-!
# Manuscript 14.119, equation (177): actual logarithmic numerator

This module links the normalized Eulerian/hyperbolic remainder directly
to the logarithm of x/(sinh x - x), without a proxy, approximation oracle
or an unproved analytic expansion.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

theorem numerator_log_exact (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log (x / (Real.sinh x - x)) =
      Real.log (6 / x ^ 2) - Real.log (1 + normalizedEpsilon x) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have htpos : 0 < x ^ 2 := pow_pos hx _
  have htne : x ^ 2 ≠ 0 := ne_of_gt htpos
  have hE := epsilon_positive_enclosure x hx hx1
  have hepspos : 0 < epsilon x :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < x ^ 2 / 6) hE.1
  have hu := normalized_epsilon_bounds x hx hx1
  have h1u : 0 < 1 + normalizedEpsilon x := by linarith [hu.1]
  have hdiff : Real.sinh x - x = x * epsilon x := by
    dsimp [epsilon]
    field_simp [hxne] <;> ring
  have hfactor := epsilon_factorization x hx
  have hratio :
      x / (Real.sinh x - x) =
        (6 / x ^ 2) / (1 + normalizedEpsilon x) := by
    rw [hdiff, hfactor]
    field_simp [hxne, htne, ne_of_gt h1u] <;> ring
  rw [hratio]
  exact Real.log_div
    (ne_of_gt (div_pos (by norm_num) htpos)) (ne_of_gt h1u)

/-- The exact numerator of the Parry-index logarithm has a uniform
first-order remainder for 0 < x ≤ 1. -/
theorem numerator_log_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (x / (Real.sinh x - x)) -
      (Real.log (6 / x ^ 2) - x ^ 2 / 20)| ≤ x ^ 4 / 100 := by
  rw [numerator_log_exact x hx hx1]
  have hid :
      (Real.log (6 / x ^ 2) - Real.log (1 + normalizedEpsilon x)) -
        (Real.log (6 / x ^ 2) - x ^ 2 / 20) =
          -(Real.log (1 + normalizedEpsilon x) - x ^ 2 / 20) := by
    ring
  rw [hid, abs_neg]
  exact normalized_log_taylor x hx hx1

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.numerator_log_exact
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.numerator_log_taylor

end SpecialImaginaryPoint.V14119Asymptotic177
