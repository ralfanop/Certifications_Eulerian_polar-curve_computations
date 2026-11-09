import SpecialImaginaryPoint.V14119Asymptotic177Taylor
import SpecialImaginaryPoint.V14119Asymptotic177Log

/-!
# Manuscript 14.119 (177) — positive and normalized hyperbolic remainder

These estimates turn the kernel-certified sinh Taylor remainder into a
strictly positive factorization suitable for the numerator logarithm of
the Parry index.

All estimates are uniform for 0 < x ≤ 1 and do not assume a Taylor series
or numerical approximation for the logarithmic quotient itself.
-/

namespace SpecialImaginaryPoint.V14119Asymptotic177

noncomputable def epsilon (x : ℝ) : ℝ := (Real.sinh x - x) / x

noncomputable def normalizedEpsilon (x : ℝ) : ℝ :=
  6 * epsilon x / x ^ 2 - 1

theorem epsilon_positive_enclosure (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    x ^ 2 / 6 ≤ epsilon x ∧
      epsilon x ≤ x ^ 2 / 6 + (x ^ 2) ^ 2 / 96 := by
  let t : ℝ := x ^ 2
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1 - x by linarith)]
  have ht3 : t ^ 3 ≤ t ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1 - t by linarith)]
  have heq :
      epsilon x - t / 6 - t ^ 2 / 120 =
        (Real.sinh x - x) / x - x ^ 2 / 6 - x ^ 4 / 120 := by
    dsimp [epsilon, t]
    ring
  have hpow : t ^ 3 / 4410 = x ^ 6 / 4410 := by
    dsimp [t]
    ring
  have hraw := epsilon_taylor_bound x hx hx1
  have hE : |epsilon x - t / 6 - t ^ 2 / 120| ≤ t ^ 3 / 4410 := by
    rw [heq, hpow]
    exact hraw
  obtain ⟨hl, hu⟩ := abs_le.mp hE
  constructor
  · change t / 6 ≤ epsilon x
    linarith [ht3, sq_nonneg t]
  · change epsilon x ≤ t / 6 + t ^ 2 / 96
    linarith [ht3, sq_nonneg t]

theorem normalized_epsilon_bounds (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ normalizedEpsilon x ∧ normalizedEpsilon x ≤ x ^ 2 / 16 := by
  have hE := epsilon_positive_enclosure x hx hx1
  have ht : 0 < x ^ 2 := pow_pos hx _
  have hlow : 1 ≤ 6 * epsilon x / x ^ 2 := by
    apply (le_div_iff₀ ht).2
    nlinarith [hE.1]
  have hhigh : 6 * epsilon x / x ^ 2 ≤ 1 + x ^ 2 / 16 := by
    apply (div_le_iff₀ ht).2
    nlinarith [hE.2]
  constructor
  · change 0 ≤ 6 * epsilon x / x ^ 2 - 1
    linarith
  · change 6 * epsilon x / x ^ 2 - 1 ≤ x ^ 2 / 16
    linarith

theorem epsilon_factorization (x : ℝ) (hx : 0 < x) :
    epsilon x = (x ^ 2 / 6) * (1 + normalizedEpsilon x) := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have htne : x ^ 2 ≠ 0 := pow_ne_zero _ hxne
  dsimp [normalizedEpsilon]
  field_simp [htne]
  ring

#print axioms SpecialImaginaryPoint.V14119Asymptotic177.epsilon_positive_enclosure
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.normalized_epsilon_bounds
#print axioms SpecialImaginaryPoint.V14119Asymptotic177.epsilon_factorization

end SpecialImaginaryPoint.V14119Asymptotic177
