import SpecialImaginaryPoint.V14119Asymptotic177Epsilon
import SpecialImaginaryPoint.V14119ParryAnalyticInputsX20
import SpecialImaginaryPoint.V14119ParryResidualTransferX20

/-! Frozen M14.119, equation (225). Discharge the actual denominator
nondegeneracy and high-order scalar log errors, reusing the proved positive
hyperbolic enclosures and Taylor theorem. The remaining gate is conversion
of the composed finite Taylor polynomials to their degree-12/11 truncations. -/

noncomputable section
namespace Manuscript14.ParryActualLog
open SpecialImaginaryPoint.V14119Asymptotic177
open Manuscript14.ParryAnalyticInputs Manuscript14.ParryResidual

def beta (x : ℝ) : ℝ := Real.sinh x / x

def logTaylor (n : ℕ) (y : ℝ) : ℝ :=
  -(∑ i ∈ Finset.range n, (-y)^(i+1) / ((i:ℝ)+1))

theorem beta_eq (x : ℝ) (hx : 0 < x) : beta x = 1 + epsilon x := by
  unfold beta epsilon
  field_simp [hx.ne'] <;> ring

theorem square_le_one (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    x^2 ≤ 1 := by
  nlinarith [mul_nonneg hx.le (show 0 ≤ 1-x by linarith)]

theorem epsilon_small (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    0 ≤ epsilon x ∧ epsilon x ≤ x^2/5 := by
  have hE := epsilon_positive_enclosure x hx hx1
  have ht1 := square_le_one x hx hx1
  have h4 : (x^2)^2 ≤ x^2 :=
    by nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr ht1)]
  exact ⟨(by positivity : 0 ≤ x^2/6).trans hE.1, by linarith [hE.2, h4]⟩

theorem beta_gt_one (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    1 < beta x := by
  rw [beta_eq x hx]
  have h := (epsilon_positive_enclosure x hx hx1).1
  have ht : 0 < x^2/6 := by positivity
  linarith

/-- The denominator bound required by the exact degree-11 residual transfer
is now stated for the actual hyperbolic profile on the whole interval. -/
theorem denominator_lower (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (1:ℝ)/12 ≤ Real.log (beta x)/x^2 := by
  have ht : 0 < x^2 := sq_pos_of_pos hx
  have ht1 := square_le_one x hx hx1
  have hE := epsilon_positive_enclosure x hx hx1
  have hsmall := epsilon_small x hx hx1
  have hlog := Real.le_log_one_add_of_nonneg hsmall.1
  have hD : 0 < epsilon x + 2 := by linarith [hsmall.1]
  have hm : x^2 * (epsilon x + 2) ≤ 4*x^2 := by
    have he : epsilon x ≤ 2 := by linarith [hsmall.2,ht1]
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr he)]
  have hlow : x^2/12 ≤ 2*epsilon x/(epsilon x+2) := by
    apply (le_div_iff₀ hD).2
    nlinarith [hE.1,hm]
  apply (le_div_iff₀ ht).2
  rw [beta_eq x hx]
  have h := hlow.trans hlog
  linarith

theorem denominator_abs_lower (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    (1:ℝ)/12 ≤ |Real.log (beta x)/x^2| :=
  (denominator_lower x hx hx1).trans (le_abs_self _)

theorem normalized_beta_eq (x : ℝ) (hx : 0 < x) :
    6*(beta x-1)/x^2 = 1+normalizedEpsilon x := by
  rw [beta_eq x hx]
  unfold normalizedEpsilon
  ring

/-- Actual normalized log denominator, before truncating the finite
composition in x². This is uniform, not a pointwise sample. -/
theorem denominator_log_composed (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (beta x)/x^2-logTaylor 12 (epsilon x)/x^2| ≤
      2*(x^2)^12 := by
  have ht : 0 < x^2 := sq_pos_of_pos hx
  have ht1 := square_le_one x hx hx1
  have hε := epsilon_small x hx hx1
  have hhalf : epsilon x ≤ 1/2 := by linarith [hε.2,ht1]
  have hpow : (epsilon x)^13 ≤ (x^2)^13 :=
    pow_le_pow_left₀ hε.1 (by linarith [hε.2,ht.le]) 13
  have hlog : |Real.log (1+epsilon x)-logTaylor 12 (epsilon x)| ≤
      2*(epsilon x)^13 := by
    simpa [logTaylor, sub_neg_eq_add] using log_one_add_taylor (epsilon x) hε.1 hhalf 12
  rw [beta_eq x hx, ← sub_div, abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).2
  calc
    _ ≤ 2*(epsilon x)^13 := hlog
    _ ≤ 2*(x^2)^13 := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 2*(x^2)^12*x^2 := by ring

/-- Actual normalized log numerator, before truncating the finite
composition in x². -/
theorem numerator_log_composed (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |Real.log (6*(beta x-1)/x^2)-logTaylor 11 (normalizedEpsilon x)| ≤
      2*(x^2)^12 := by
  have ht : 0 ≤ x^2 := sq_nonneg x
  have ht1 := square_le_one x hx hx1
  have he := normalized_epsilon_bounds x hx hx1
  have hhalf : normalizedEpsilon x ≤ 1/2 := by linarith [he.2,ht1]
  have hpow : (normalizedEpsilon x)^12 ≤ (x^2)^12 :=
    pow_le_pow_left₀ he.1 (by linarith [he.2,ht]) 12
  have hlog : |Real.log (1+normalizedEpsilon x)-logTaylor 11 (normalizedEpsilon x)| ≤
      2*(normalizedEpsilon x)^12 := by
    simpa [logTaylor, sub_neg_eq_add] using
      log_one_add_taylor (normalizedEpsilon x) he.1 hhalf 11
  rw [normalized_beta_eq x hx]
  exact hlog.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))

/-- The logarithmic scale is uniformly ≥1 for x≤1, as needed by #371. -/
theorem scale_lower (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    1 ≤ Real.log (6/x^2) := by
  have ht : 0 < x^2 := sq_pos_of_pos hx
  have h6 : (3:ℝ) ≤ 6/x^2 := by
    apply (le_div_iff₀ ht).2
    linarith [square_le_one x hx hx1]
  let z : ℝ := 6/x^2-1
  have hz2 : 2 ≤ z := by dsimp [z]; linarith
  have hz0 : 0 ≤ z := by linarith
  have hzpos : 0 < z+2 := by linarith
  have hl : 1 ≤ 2*z/(z+2) := by
    apply (le_div_iff₀ hzpos).2
    linarith
  have hlog := Real.le_log_one_add_of_nonneg hz0
  have he : 1+z = 6/x^2 := by dsimp [z]; ring
  rw [he] at hlog
  exact hl.trans hlog

/-- Reduction of the entire remainder to the two remaining finite
composed-polynomial estimates. No denominator or logarithmic scale
hypothesis is left. -/
theorem actual_parry_reduction (x K L : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hp : |logTaylor 12 (epsilon x)/x^2-A12 (x^2)| ≤ K*(x^2)^12)
    (hc : |logTaylor 11 (normalizedEpsilon x)-C12 (x^2)| ≤ L*(x^2)^12) :
    |Real.log (1/(beta x-1))/Real.log (beta x) -
      (P12 (x^2)*Real.log (6/x^2)+R12 (x^2))/x^2| ≤
        (168*(K+2)+12*(L+2)+25)*(x^2)^11*Real.log (6/x^2) := by
  have hda : |Real.log (beta x)/x^2-A12 (x^2)| ≤ (K+2)*(x^2)^12 := by
    calc
      _ = |(Real.log (beta x)/x^2-logTaylor 12 (epsilon x)/x^2)+
          (logTaylor 12 (epsilon x)/x^2-A12 (x^2))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2*(x^2)^12+K*(x^2)^12 :=
        add_le_add (denominator_log_composed x hx hx1) hp
      _ = _ := by ring
  have hC : |Real.log (6*(beta x-1)/x^2)-C12 (x^2)| ≤ (L+2)*(x^2)^12 := by
    calc
      _ = |(Real.log (6*(beta x-1)/x^2)-logTaylor 11 (normalizedEpsilon x))+
           (logTaylor 11 (normalizedEpsilon x)-C12 (x^2))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 2*(x^2)^12+L*(x^2)^12 :=
        add_le_add (numerator_log_composed x hx hx1) hc
      _ = _ := by ring
  exact parry_expansion_transfer (x^2) (beta x) (K+2) (L+2)
    (sq_pos_of_pos hx) (square_le_one x hx hx1) (beta_gt_one x hx hx1)
    (by linarith) (by linarith) (scale_lower x hx hx1)
    (denominator_abs_lower x hx hx1) hda hC

#print axioms beta_eq
#print axioms square_le_one
#print axioms epsilon_small
#print axioms beta_gt_one
#print axioms denominator_lower
#print axioms denominator_abs_lower
#print axioms normalized_beta_eq
#print axioms denominator_log_composed
#print axioms numerator_log_composed
#print axioms scale_lower
#print axioms actual_parry_reduction
end Manuscript14.ParryActualLog
