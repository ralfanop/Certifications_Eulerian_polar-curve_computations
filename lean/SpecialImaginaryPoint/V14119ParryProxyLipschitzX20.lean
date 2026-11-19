import SpecialImaginaryPoint.V14119ParryActualLogX20
import SpecialImaginaryPoint.V14119ParryActualLogsX20

/-! M14 (225): rigorous substitution into the finite logarithm polynomials.
The remaining exact coefficient-residual estimates audited in #448 are
explicit inputs to the last theorem, not asserted as Lean-verified here. -/
noncomputable section
namespace Manuscript14.ParryProxy
open SpecialImaginaryPoint.V14119Asymptotic177
open Manuscript14.ParryAnalyticInputs Manuscript14.ParryActualLog
open Manuscript14.ParryResidual

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem pow_difference_bound (v w : ℝ) (hv : |v| ≤ 1) (hw : |w| ≤ 1)
    (k : ℕ) : |v^k-w^k| ≤ (k:ℝ)*|v-w| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs : v^(k+1)-w^(k+1) =
        v*(v^k-w^k)+(v-w)*w^k := by simp only [pow_succ]; ring
    have hvk : |v * (v^k-w^k)| ≤ (k:ℝ)*|v-w| := by
      rw [abs_mul]
      calc
        _ ≤ 1 * |v^k-w^k| := mul_le_mul_of_nonneg_right hv (abs_nonneg _)
        _ ≤ _ := by simpa only [one_mul] using ih
    have hwk : |(v-w)*w^k| ≤ |v-w| := by
      rw [abs_mul, abs_pow]
      exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hw)
    rw [hs]
    calc
      _ ≤ |v*(v^k-w^k)|+|(v-w)*w^k| := abs_add_le _ _
      _ ≤ (k:ℝ)*|v-w|+|v-w| := add_le_add hvk hwk
      _ = _ := by push_cast; ring

/-- Each summand of the finite alternating logarithm polynomial is
one-Lipschitz on the closed real unit interval. -/
theorem log_term_difference_bound (v w : ℝ) (hv : |v| ≤ 1) (hw : |w| ≤ 1)
    (k : ℕ) :
    |(-v)^(k+1)/((k:ℝ)+1)-(-w)^(k+1)/((k:ℝ)+1)| ≤ |v-w| := by
  have hp := pow_difference_bound (-v) (-w)
    (by simpa only [abs_neg] using hv) (by simpa only [abs_neg] using hw) (k+1)
  have ha : |-v- -w|=|v-w| := by
    rw [show -v- -w = -(v-w) by ring, abs_neg]
  rw [ha] at hp
  push_cast at hp
  have hd : 0 < (k:ℝ)+1 := by positivity
  rw [← sub_div, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).2
  calc
    _ ≤ ((k:ℝ)+1)*|v-w| := hp
    _ = _ := by ring

theorem logTaylor_lipschitz (v w : ℝ) (hv : |v| ≤ 1) (hw : |w| ≤ 1)
    (n : ℕ) : |logTaylor n v-logTaylor n w| ≤ (n:ℝ)*|v-w| := by
  induction n with
  | zero => simp [logTaylor]
  | succ n ih =>
    let d := (-v)^(n+1)/((n:ℝ)+1)-(-w)^(n+1)/((n:ℝ)+1)
    have hd : |d| ≤ |v-w| := log_term_difference_bound v w hv hw n
    have hs : logTaylor (n+1) v-logTaylor (n+1) w =
        (logTaylor n v-logTaylor n w)-d := by
      simp only [logTaylor, Finset.sum_range_succ, d]
      ring
    rw [hs]
    calc
      _ ≤ |logTaylor n v-logTaylor n w|+|d| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (logTaylor n v-logTaylor n w) (-d)
      _ ≤ (n:ℝ)*|v-w|+|v-w| := add_le_add ih hd
      _ = _ := by push_cast; ring

def E (t : ℝ) : ℝ := ∑ j ∈ Finset.range 12, t^(j+1)/(Nat.factorial (2*j+3):ℝ)
def U (t : ℝ) : ℝ := ∑ j ∈ Finset.range 11, 6*t^(j+1)/(Nat.factorial (2*j+5):ℝ)

/-- These are the actual degree-12 and degree-11 proxy polynomials
used in the exact rational composition audit. -/
theorem E_eq (x : ℝ) (hx : x ≠ 0) : E (x^2) = sinh25 x/x-1 := by
  norm_num [E, sinh25, Finset.sum_range_succ, Nat.factorial]
  field_simp [hx] <;> ring

theorem U_eq (x : ℝ) (hx : x ≠ 0) : U (x^2) = 6*(sinh25 x/x-1)/x^2-1 := by
  norm_num [U, sinh25, Finset.sum_range_succ, Nat.factorial]
  field_simp [hx] <;> ring

theorem E_error (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |epsilon x-E (x^2)| ≤ x^26 := by
  rw [E_eq x hx.ne']
  exact Manuscript14.ParryActualLogs.epsilon_polynomial_proxy x hx hx1

theorem U_error (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    |normalizedEpsilon x-U (x^2)| ≤ 6*x^24 := by
  rw [U_eq x hx.ne']
  exact Manuscript14.ParryActualLogs.normalized_epsilon_polynomial_proxy x hx hx1

theorem denominator_proxy_substitution (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    |logTaylor 12 (epsilon x)/x^2-logTaylor 12 (E (x^2))/x^2| ≤
      12*(x^2)^12 := by
  have hxle : x ≤ 1 := by linarith
  have he := epsilon_small x hx hxle
  have hx2 := square_le_one x hx hxle
  have habs : |epsilon x| ≤ 1/5 := by rw [abs_of_nonneg he.1]; linarith [he.2]
  have hx26 : x^26 ≤ (1/2:ℝ)^26 := pow_le_pow_left₀ hx.le hx1 _
  have herror := E_error x hx hxle
  have hE : |E (x^2)| ≤ 1 := by
    have hs : E (x^2) = epsilon x + (-(epsilon x-E (x^2))) := by ring
    rw [hs]
    have h := abs_add_le (epsilon x) (-(epsilon x-E (x^2)))
    rw [abs_neg] at h
    norm_num at hx26
    linarith [h, habs, herror]
  have h := logTaylor_lipschitz (epsilon x) (E (x^2))
    (by linarith [habs]) hE 12
  have ht : 0 < x^2 := sq_pos_of_pos hx
  rw [← sub_div, abs_div, abs_of_pos ht]
  apply (div_le_iff₀ ht).2
  calc
    _ ≤ (12:ℝ)*|epsilon x-E (x^2)| := by simpa using h
    _ ≤ 12*x^26 := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = _ := by ring

theorem numerator_proxy_substitution (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2) :
    |logTaylor 11 (normalizedEpsilon x)-logTaylor 11 (U (x^2))| ≤ 66*(x^2)^12 := by
  have hxle : x ≤ 1 := by linarith
  have he := normalized_epsilon_bounds x hx hxle
  have hx2 := square_le_one x hx hxle
  have habs : |normalizedEpsilon x| ≤ 1/16 := by
    rw [abs_of_nonneg he.1]; linarith [he.2]
  have hx24 : x^24 ≤ (1/2:ℝ)^24 := pow_le_pow_left₀ hx.le hx1 _
  have herror := U_error x hx hxle
  have hU : |U (x^2)| ≤ 1 := by
    have hs : U (x^2) = normalizedEpsilon x + (-(normalizedEpsilon x-U (x^2))) := by ring
    rw [hs]
    have h := abs_add_le (normalizedEpsilon x) (-(normalizedEpsilon x-U (x^2)))
    rw [abs_neg] at h
    norm_num at hx24
    linarith [h, habs, herror]
  have h := logTaylor_lipschitz (normalizedEpsilon x) (U (x^2))
    (by linarith [habs]) hU 11
  calc
    _ ≤ (11:ℝ)*|normalizedEpsilon x-U (x^2)| := by simpa using h
    _ ≤ 11*(6*x^24) := mul_le_mul_of_nonneg_left herror (by norm_num)
    _ = _ := by ring

/-- Reduction now to exact finite-polynomial residuals ONLY.
The bounds with coefficient 1 are weaker than the exact 1/1000 audit
in #448, but still have to be independently kernel-proved. -/
theorem parry_from_finite_residuals (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1/2)
    (hA : |logTaylor 12 (E (x^2))/x^2-A12 (x^2)| ≤ (x^2)^12)
    (hC : |logTaylor 11 (U (x^2))-C12 (x^2)| ≤ (x^2)^12) :
    |Real.log (1/(beta x-1))/Real.log (beta x) -
      (P12 (x^2)*Real.log (6/x^2)+R12 (x^2))/x^2| ≤
        3373*(x^2)^11*Real.log (6/x^2) := by
  have hD : |logTaylor 12 (epsilon x)/x^2-A12 (x^2)| ≤ 13*(x^2)^12 := by
    calc
      _ = |(logTaylor 12 (epsilon x)/x^2-logTaylor 12 (E (x^2))/x^2)+
        (logTaylor 12 (E (x^2))/x^2-A12 (x^2))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 12*(x^2)^12+(x^2)^12 := add_le_add (denominator_proxy_substitution x hx hx1) hA
      _ = _ := by ring
  have hN : |logTaylor 11 (normalizedEpsilon x)-C12 (x^2)| ≤ 67*(x^2)^12 := by
    calc
      _ = |(logTaylor 11 (normalizedEpsilon x)-logTaylor 11 (U (x^2)))+
          (logTaylor 11 (U (x^2))-C12 (x^2))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ 66*(x^2)^12+(x^2)^12 := add_le_add (numerator_proxy_substitution x hx hx1) hC
      _ = _ := by ring
  have h := actual_parry_reduction x 13 67 hx (by linarith) (by norm_num) (by norm_num) hD hN
  norm_num at h ⊢
  exact h

#print axioms pow_difference_bound
#print axioms log_term_difference_bound
#print axioms logTaylor_lipschitz
#print axioms E_eq
#print axioms U_eq
#print axioms E_error
#print axioms U_error
#print axioms denominator_proxy_substitution
#print axioms numerator_proxy_substitution
#print axioms parry_from_finite_residuals
end Manuscript14.ParryProxy
