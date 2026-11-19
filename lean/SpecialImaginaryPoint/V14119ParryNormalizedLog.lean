import SpecialImaginaryPoint.V14119Asymptotic177Epsilon
import SpecialImaginaryPoint.V14119ParryAnalyticInputsX20
import SpecialImaginaryPoint.V14119ParryResidualTransferX20

/-! Actual normalized logarithm bounds for the high-order Parry expansion.
Reuses the proved low-order positive enclosures (#75) and high-order generic
logarithm remainder (#362). The polynomial composition gates remain explicit. -/
namespace Manuscript14.ParryNormalizedLog

open SpecialImaginaryPoint.V14119Asymptotic177
open Manuscript14.ParryAnalyticInputs Manuscript14.ParryResidual

theorem profile_eq (x : ℝ) (hx : 0 < x) :
    Real.sinh x / x = 1 + epsilon x := by
  dsimp [epsilon]
  field_simp [hx.ne'] <;> ring

theorem profile_gt_one (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    1 < Real.sinh x / x := by
  rw [profile_eq x hx]
  have h := (epsilon_positive_enclosure x hx hx1).1
  have hp : 0 < x^2 / 6 := by positivity
  linarith

/-- Uniform positive lower bound required by the exact quotient transfer. -/
theorem normalized_denominator_lower (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (1:ℝ)/12 ≤ |Real.log (Real.sinh x / x) / x^2| := by
  let t : ℝ := x^2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp [t]
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]
  have he : t/6 ≤ epsilon x := (epsilon_positive_enclosure x hx hx1).1
  have hpos : 0 ≤ t/6 := by positivity
  have hmono : Real.log (1+t/6) ≤ Real.log (Real.sinh x / x) := by
    apply Real.log_le_log (by positivity)
    rw [profile_eq x hx]
    linarith
  have hlog := Real.le_log_one_add_of_nonneg hpos
  have hrat : t/12 ≤ 2*(t/6)/(t/6+2) := by
    apply (le_div_iff₀ (show 0 < t/6+2 by positivity)).2
    nlinarith [mul_nonneg ht.le (show 0 ≤ 1-t by linarith)]
  have hlower : t/12 ≤ Real.log (Real.sinh x / x) :=
    hrat.trans (hlog.trans hmono)
  have hq : (1:ℝ)/12 ≤ Real.log (Real.sinh x / x) / t := by
    apply (le_div_iff₀ ht).2
    linarith
  exact hq.trans (le_abs_self _)

theorem epsilon_upper_quarter (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ epsilon x ∧ epsilon x ≤ x^2/4 := by
  have h := epsilon_positive_enclosure x hx hx1
  have ht1 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]
  have ht2 : (x^2)^2 ≤ x^2 := by
    nlinarith [mul_nonneg (sq_nonneg x) (show 0 ≤ 1-x^2 by linarith)]
  constructor
  · linarith [h.1, sq_nonneg x]
  · linarith [h.2, ht2, sq_nonneg x]

/-- Actual denominator logarithm: the truncation in the true epsilon has
a rigorous thirteenth-order bound, not just a formal series identity. -/
theorem actual_log_profile_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (Real.sinh x / x) +
      ∑ i ∈ Finset.range 12, (-epsilon x)^(i+1)/((i:ℝ)+1)| ≤
      2 * (x^2/4)^13 := by
  have he := epsilon_upper_quarter x hx hx1
  have ht1 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]
  have hehalf : epsilon x ≤ 1/2 := by linarith [he.2]
  rw [profile_eq x hx]
  apply (log_one_add_taylor (epsilon x) he.1 hehalf 12).trans
  change 2 * epsilon x ^ 13 ≤ 2 * (x^2/4)^13
  gcongr <;> first | exact he.1 | exact he.2 | positivity

theorem normalized_profile_eq (x : ℝ) (hx : 0 < x) :
    6*(Real.sinh x/x-1)/x^2 = 1+normalizedEpsilon x := by
  rw [profile_eq x hx]
  unfold normalizedEpsilon
  ring

/-- Actual normalized numerator logarithm, with uniform twelfth-order error. -/
theorem actual_log_normalized_taylor (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (6*(Real.sinh x/x-1)/x^2) +
      ∑ i ∈ Finset.range 11, (-normalizedEpsilon x)^(i+1)/((i:ℝ)+1)| ≤
      2*(x^2/16)^12 := by
  have he := normalized_epsilon_bounds x hx hx1
  have ht1 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]
  have hehalf : normalizedEpsilon x ≤ 1/2 := by linarith [he.2]
  rw [normalized_profile_eq x hx]
  apply (log_one_add_taylor (normalizedEpsilon x) he.1 hehalf 11).trans
  change 2 * normalizedEpsilon x ^ 12 ≤ 2 * (x^2/16)^12
  gcongr <;> first | exact he.1 | exact he.2 | positivity

/-- Logarithmic scale needed by the quotient transfer, uniformly on 0<x≤1. -/
theorem parry_log_scale (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    1 ≤ Real.log (6/x^2) := by
  have ht : 0 < x^2 := pow_pos hx _
  have ht1 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]
  have hlarge : (3:ℝ) ≤ 6/x^2 := by
    apply (le_div_iff₀ ht).2
    linarith
  let z : ℝ := 6/x^2-1
  have hz2 : 2 ≤ z := by dsimp [z]; linarith
  have hz0 : 0 ≤ z := by linarith
  have hsmall : 1 ≤ 2*z/(z+2) := by
    apply (le_div_iff₀ (show 0 < z+2 by linarith)).2
    linarith
  have hlog := Real.le_log_one_add_of_nonneg hz0
  have harg : 1+z = 6/x^2 := by dsimp [z]; ring
  rw [harg] at hlog
  exact hsmall.trans hlog

/-- All positivity and logarithmic-scale gates discharged for the actual
hyperbolic profile. ONLY the two polynomial composition remainder bounds
remain hypotheses, and are not asserted by this theorem. -/
theorem actual_parry_transfer (x K L : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hA : |Real.log (Real.sinh x/x)/x^2-A12 (x^2)| ≤ K*(x^2)^12)
    (hC : |Real.log (6*(Real.sinh x/x-1)/x^2)-C12 (x^2)| ≤ L*(x^2)^12) :
    |Real.log (1/(Real.sinh x/x-1))/Real.log (Real.sinh x/x) -
      (P12 (x^2)*Real.log (6/x^2)+R12 (x^2))/x^2| ≤
      (168*K+12*L+25)*(x^2)^11*Real.log (6/x^2) := by
  have ht1 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]
  exact parry_expansion_transfer (x^2) (Real.sinh x/x) K L
    (pow_pos hx _) ht1 (profile_gt_one x hx hx1) hK hL
    (parry_log_scale x hx hx1) (normalized_denominator_lower x hx hx1) hA hC

#print axioms profile_eq
#print axioms profile_gt_one
#print axioms normalized_denominator_lower
#print axioms epsilon_upper_quarter
#print axioms actual_log_profile_taylor
#print axioms normalized_profile_eq
#print axioms actual_log_normalized_taylor
#print axioms parry_log_scale
#print axioms actual_parry_transfer
end Manuscript14.ParryNormalizedLog
