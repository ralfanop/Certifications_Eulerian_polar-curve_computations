import GegenbauerFock.KummerPochhammer

/-!
# V007: absolute convergence of the genuine unregularized Kummer series

For λ>0, all coefficients (1/2)_n/(λ+1)_n lie in [0,1].
Comparison with exp(|z|) proves convergence of the complete real
power series for every real argument z, including negative z.

This concerns convergence and the correct Pochhammer coefficients; it
does not substitute for proving ultraspherical moments or the integral
formula.
-/

namespace GegenbauerFock.KummerCoefficients

/-- The generalized Kummer series is absolutely summable for every
real argument z, not only for nonnegative arguments. -/
theorem kummerSeries_summable_all_real
    (lam z : ℝ) (hlam : 0 < lam) :
    Summable (fun n : ℕ =>
      ratio lam n * (z ^ n / (Nat.factorial n : ℝ))) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le
  · intro n
    exact norm_nonneg _
  · intro n
    have ht : 0 ≤ |z| ^ n / (Nat.factorial n : ℝ) := by positivity
    calc
      ‖ratio lam n * (z ^ n / (Nat.factorial n : ℝ))‖ =
          ratio lam n * (|z| ^ n / (Nat.factorial n : ℝ)) := by
            simp [Real.norm_eq_abs, abs_mul, abs_div, abs_pow,
              abs_of_nonneg (ratio_nonneg lam hlam n)]
      _ ≤ 1 * (|z| ^ n / (Nat.factorial n : ℝ)) :=
        mul_le_mul_of_nonneg_right (ratio_le_one lam hlam n) ht
      _ = |z| ^ n / (Nat.factorial n : ℝ) := by ring
  · exact Real.summable_pow_div_factorial |z|

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_summable_all_real

end GegenbauerFock.KummerCoefficients
