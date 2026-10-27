import GegenbauerFock.UltrasphericalKummerBridge
import GegenbauerFock.OperatorExpBound

/-!
# V007: two-sided scalar energy bounds for the actual infinite Fock map

These theorems concern the exact, kernel-certified coefficient-row
Hilbert energy, not the as-yet unformalized abstract Schatten S₂ norm.
They hold for every λ>0 and α>0 without requiring the outstanding
closed form of general ultraspherical moments.
-/

namespace GegenbauerFock.GeneralUltrasphericalFock

private theorem evenMomentWeighted_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Summable (fun n : ℕ => Ultraspherical.evenMoment lam n *
      ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ))) := by
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (Ultraspherical.evenMoment_nonneg lam n) (by positivity)
  · intro n
    simpa using mul_le_mul_of_nonneg_right
      (Ultraspherical.evenMoment_le_one lam hlam n)
      (by positivity : 0 ≤ (1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ))
  · exact Real.summable_pow_div_factorial (1 / (4 * alpha))

/-- The zeroth ultraspherical moment forces the row energy to be at least one. -/
theorem rowEnergy_ge_one
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    1 ≤ rowEnergy lam alpha hlam ha := by
  have hs := evenMomentWeighted_summable lam alpha hlam ha
  have htail : 0 ≤ ∑' n : ℕ, Ultraspherical.evenMoment lam (n + 1) *
      ((1 / (4 * alpha)) ^ (n + 1) /
        (Nat.factorial (n + 1) : ℝ)) :=
    tsum_nonneg (fun n =>
      mul_nonneg (Ultraspherical.evenMoment_nonneg lam (n + 1)) (by positivity))
  rw [rowEnergy_eq_evenMoment_series lam alpha hlam ha, hs.tsum_eq_zero_add]
  simpa [Ultraspherical.evenMoment_zero lam hlam] using
    (show (1 : ℝ) ≤ 1 + ∑' n : ℕ,
      Ultraspherical.evenMoment lam (n + 1) *
        ((1 / (4 * alpha)) ^ (n + 1) /
          (Nat.factorial (n + 1) : ℝ))
      from (le_add_iff_nonneg_right _).mpr htail)

/-- The ultraspherical row energy is bounded by the full exponential. -/
theorem rowEnergy_le_exp
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha ≤ Real.exp (1 / (4 * alpha)) := by
  have hs := evenMomentWeighted_summable lam alpha hlam ha
  have hs_exp := Real.summable_pow_div_factorial (1 / (4 * alpha))
  have hle : ∀ n : ℕ, Ultraspherical.evenMoment lam n *
      ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ)) ≤
      (1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ) := by
    intro n
    simpa using mul_le_mul_of_nonneg_right
      (Ultraspherical.evenMoment_le_one lam hlam n)
      (by positivity : 0 ≤ (1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ))
  rw [rowEnergy_eq_evenMoment_series lam alpha hlam ha]
  calc
    (∑' n : ℕ, Ultraspherical.evenMoment lam n *
      ((1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ))) ≤
      ∑' n : ℕ, (1 / (4 * alpha)) ^ n / (Nat.factorial n : ℝ) :=
      hs.tsum_le_tsum hle hs_exp
    _ = Real.exp (1 / (4 * alpha)) := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_ge_one
#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_le_exp

end GegenbauerFock.GeneralUltrasphericalFock
