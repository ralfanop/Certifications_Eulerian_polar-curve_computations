import GegenbauerFock.KummerEntireReal

/-!
# V007: quantitative comparison bounds for the unregularized Kummer series

For λ>0 and z≥0, the actual positive Pochhammer coefficient
series lies between its constant term and the real exponential.
This is a scalar prerequisite for quantitative spectral trace bounds,
not a replacement for the missing ultraspherical moment formula.
-/

namespace GegenbauerFock.KummerCoefficients

/-- The real Kummer value is at least one for nonnegative arguments. -/
theorem kummerSeries_ge_one (lam z : ℝ)
    (hlam : 0 < lam) (hz : 0 ≤ z) :
    1 ≤ kummerSeries lam z := by
  have hs := kummerSeries_summable lam z hlam hz
  have htail : 0 ≤
      ∑' n : ℕ,
        ratio lam (n+1) * (z ^ (n+1) / (Nat.factorial (n+1) : ℝ)) :=
    tsum_nonneg (fun n => mul_nonneg
      (ratio_nonneg lam hlam (n+1)) (by positivity))
  unfold kummerSeries
  rw [hs.tsum_eq_zero_add]
  simpa using (show (1 : ℝ) ≤ 1 + ∑' n : ℕ,
      ratio lam (n+1) * (z ^ (n+1) / (Nat.factorial (n+1) : ℝ))
    from (le_add_iff_nonneg_right _).mpr htail)

/-- The unregularized Kummer value is bounded by exp(z) for z≥0. -/
theorem kummerSeries_le_exp (lam z : ℝ)
    (hlam : 0 < lam) (hz : 0 ≤ z) :
    kummerSeries lam z ≤ Real.exp z := by
  have hs := kummerSeries_summable lam z hlam hz
  have he := Real.summable_pow_div_factorial z
  have hle : ∀ n : ℕ,
      ratio lam n * (z ^ n / (Nat.factorial n : ℝ)) ≤
        z ^ n / (Nat.factorial n : ℝ) := by
    intro n
    simpa using
      mul_le_mul_of_nonneg_right (ratio_le_one lam hlam n)
        (by positivity : 0 ≤ z ^ n / (Nat.factorial n : ℝ))
  have hb := hs.tsum_le_tsum hle he
  unfold kummerSeries
  calc
    (∑' n : ℕ, ratio lam n * (z ^ n / (Nat.factorial n : ℝ))) ≤
        ∑' n : ℕ, z ^ n / (Nat.factorial n : ℝ) := hb
    _ = Real.exp z := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_ge_one
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_le_exp

end GegenbauerFock.KummerCoefficients
