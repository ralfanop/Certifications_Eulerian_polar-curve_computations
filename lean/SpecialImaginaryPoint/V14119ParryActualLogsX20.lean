import SpecialImaginaryPoint.V14119ParryAnalyticInputsX20
import SpecialImaginaryPoint.V14119Asymptotic177Epsilon

/-! Actual analytic logarithms for M14, eq. (225), label
eq:parry-index-asymptotics in the frozen 2026-11-17 manuscript.
The polynomial-composition step relating these finite sums to A12 and C12
in V14119ParryResidualTransferX20 remains a separate obligation. -/
namespace Manuscript14.ParryActualLogs

open Manuscript14.ParryAnalyticInputs
open SpecialImaginaryPoint.V14119Asymptotic177

noncomputable def logPoly (n : ℕ) (y : ℝ) : ℝ :=
  -(∑ i ∈ Finset.range n, (-y)^(i+1) / ((i:ℝ)+1))

theorem profile_eq (x : ℝ) (hx : 0 < x) :
    Real.sinh x / x = 1 + epsilon x := by
  unfold epsilon
  field_simp [ne_of_gt hx] <;> ring

theorem epsilon_small (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    0 ≤ epsilon x ∧ epsilon x ≤ x^2 ∧ epsilon x ≤ 1/2 := by
  have h := epsilon_positive_enclosure x hx (by linarith : x ≤ 1)
  have ht : x^2 ≤ 1/4 := by nlinarith [mul_nonneg hx.le (show 0 ≤ 1/2-x by linarith)]
  have h4 : (x^2)^2 ≤ x^2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-x^2 by linarith)]
  exact ⟨by linarith [h.1, sq_nonneg x], by linarith [h.2, sq_nonneg x], by linarith [h.2]⟩

theorem actual_denominator_lower (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    1/12 ≤ |Real.log (Real.sinh x / x) / x^2| := by
  have he := epsilon_small x hx hx1
  have hl := (epsilon_positive_enclosure x hx (by linarith : x ≤ 1)).1
  have hlog := Real.le_log_one_add_of_nonneg he.1
  have hrat : epsilon x / 2 ≤ 2 * epsilon x / (epsilon x + 2) := by
    apply (le_div_iff₀ (by linarith [he.1] : 0 < epsilon x + 2)).2
    nlinarith [mul_nonneg he.1 (show 0 ≤ 2-epsilon x by linarith [he.2.2])]
  have hp : x^2 / 12 ≤ Real.log (1 + epsilon x) := by linarith
  rw [profile_eq x hx]
  have ht : 0 < x^2 := pow_pos hx _
  have hn : 0 ≤ Real.log (1+epsilon x) / x^2 :=
    div_nonneg (by linarith) ht.le
  rw [abs_of_nonneg hn]
  apply (le_div_iff₀ ht).2
  linarith

theorem actual_beta_gt_one (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    1 < Real.sinh x / x := by
  rw [profile_eq x hx]
  have h := (epsilon_positive_enclosure x hx (by linarith : x ≤ 1)).1
  linarith [sq_pos_of_pos hx]

theorem actual_log_beta_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    |Real.log (Real.sinh x / x) / x^2 - logPoly 12 (epsilon x) / x^2|
      ≤ 2 * (x^2)^12 := by
  have he := epsilon_small x hx hx1
  have h := log_one_add_taylor (epsilon x) he.1 he.2.2 12
  have hp : epsilon x ^ 13 ≤ (x^2)^13 :=
    pow_le_pow_left₀ he.1 he.2.1 13
  rw [profile_eq x hx, ← sub_div, abs_div, abs_of_pos (sq_pos_of_pos hx)]
  apply (div_le_iff₀ (sq_pos_of_pos hx)).2
  calc
    _ ≤ 2 * epsilon x ^ 13 := by
      simpa only [logPoly, sub_neg_eq_add] using h
    _ ≤ 2 * (x^2)^13 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

theorem actual_log_normalized_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    |Real.log (6 * (Real.sinh x / x - 1) / x^2) -
        logPoly 11 (normalizedEpsilon x)| ≤ 2 * (x^2)^12 := by
  have he := normalized_epsilon_bounds x hx (by linarith : x ≤ 1)
  have ht : x^2 ≤ 1/4 := by nlinarith [mul_nonneg hx.le (show 0 ≤ 1/2-x by linarith)]
  have h := log_one_add_taylor (normalizedEpsilon x) he.1
      (by linarith [he.2] : normalizedEpsilon x ≤ 1/2) 11
  have hp : normalizedEpsilon x ^ 12 ≤ (x^2)^12 :=
    pow_le_pow_left₀ he.1 (by linarith [he.2, sq_nonneg x]) 12
  have heq : 6 * (Real.sinh x / x - 1) / x^2 = 1 + normalizedEpsilon x := by
    rw [profile_eq x hx]
    unfold normalizedEpsilon
    ring
  rw [heq]
  calc
    _ ≤ 2 * normalizedEpsilon x ^ 12 := by
      simpa only [logPoly, sub_neg_eq_add] using h
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)

/-- Actual log scale, not an assumption on a free parameter. -/
theorem actual_log_scale_ge_one (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    1 ≤ Real.log (6 / x^2) := by
  have ht : 0 < x^2 := pow_pos hx _
  have hts : x^2 ≤ 1/4 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1/2-x by linarith)]
  have hlarge : (3 : ℝ) ≤ 6 / x^2 := by
    apply (le_div_iff₀ ht).2
    linarith
  let z : ℝ := 6 / x^2 - 1
  have hz2 : 2 ≤ z := by dsimp [z]; linarith
  have hz0 : 0 ≤ z := by linarith
  have hsmall : 1 ≤ 2 * z / (z + 2) := by
    apply (le_div_iff₀ (by linarith : 0 < z + 2)).2
    linarith
  have hlog := Real.le_log_one_add_of_nonneg hz0
  have harg : 1 + z = 6 / x^2 := by dsimp [z]; ring
  rw [harg] at hlog
  exact hsmall.trans hlog

theorem epsilon_polynomial_proxy (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |epsilon x - (sinh25 x / x - 1)| ≤ x^26 := by
  have he : epsilon x - (sinh25 x / x - 1) =
      Real.sinh x / x - sinh25 x / x := by rw [profile_eq x hx]; ring
  rw [he]
  exact profile_taylor25 x hx hx1

theorem normalized_epsilon_polynomial_proxy (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |normalizedEpsilon x - (6 * (sinh25 x / x - 1) / x^2 - 1)| ≤ 6*x^24 := by
  have he : normalizedEpsilon x - (6 * (sinh25 x / x - 1) / x^2 - 1) =
      6 * (Real.sinh x / x - 1) / x^2 - 6 * (sinh25 x / x - 1) / x^2 := by
    rw [profile_eq x hx]
    unfold normalizedEpsilon
    ring
  rw [he]
  exact normalized_profile_taylor25 x hx hx1

#print axioms actual_log_scale_ge_one
#print axioms epsilon_polynomial_proxy
#print axioms normalized_epsilon_polynomial_proxy
#print axioms profile_eq
#print axioms epsilon_small
#print axioms actual_denominator_lower
#print axioms actual_beta_gt_one
#print axioms actual_log_beta_taylor
#print axioms actual_log_normalized_taylor
end Manuscript14.ParryActualLogs
