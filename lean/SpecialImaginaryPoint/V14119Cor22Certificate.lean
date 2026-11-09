import Mathlib
import SpecialImaginaryPoint.V14119TailBound

/-!
# Manuscript 14.119, Corollary 2.2 — all-index rational tail enclosure

This module applies the strict positive-series geometric majorant to
the exact factorial coefficients a_n = 1/[8^n(2n+1)!].

All results quantify over every N : Nat, and contain no numerical
precision parameter. The generic strict-tail comparison is now kernel-checked.
-/

namespace SpecialImaginaryPoint.V14119Cor22

noncomputable def coeff (n : ℕ) : ℝ :=
  1 / ((8 : ℝ) ^ n * (((2 * n + 1).factorial : ℕ) : ℝ))

noncomputable def denom (n : ℕ) : ℝ :=
  8 * (((2 * n + 2 : ℕ) : ℝ)) * (((2 * n + 3 : ℕ) : ℝ))

noncomputable def ratio (n : ℕ) : ℝ := 1 / denom n

noncomputable def prefixSum (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), coeff n

theorem coeff_pos (n : ℕ) : 0 < coeff n := by
  dsimp [coeff]
  positivity

theorem denom_pos (n : ℕ) : 0 < denom n := by
  dsimp [denom]
  positivity

theorem denom_strictMono : StrictMono denom := by
  intro n m hnm
  have h2n : (0 : ℝ) < (((2 * n + 3 : ℕ) : ℝ)) := by positivity
  have h2 : ((2 * n + 2 : ℕ) : ℝ) < ((2 * m + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * n + 2 < 2 * m + 2 by omega)
  have h3 : ((2 * n + 3 : ℕ) : ℝ) ≤ ((2 * m + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * n + 3 ≤ 2 * m + 3 by omega)
  dsimp [denom]
  calc
    8 * ((2 * n + 2 : ℕ) : ℝ) * ((2 * n + 3 : ℕ) : ℝ) <
      8 * ((2 * m + 2 : ℕ) : ℝ) * ((2 * n + 3 : ℕ) : ℝ) := by
        exact mul_lt_mul_of_pos_right
          (mul_lt_mul_of_pos_left h2 (by norm_num)) h2n
    _ ≤ 8 * ((2 * m + 2 : ℕ) : ℝ) * ((2 * m + 3 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

theorem ratio_antitone : Antitone ratio := by
  intro n m hnm
  have hden : denom n ≤ denom m := by
    rcases eq_or_lt_of_le hnm with h | h
    · simp [h]
    · exact (denom_strictMono h).le
  exact one_div_le_one_div_of_le (denom_pos n) hden

theorem ratio_strict_anti_step (k : ℕ) : ratio (k + 1) < ratio k := by
  exact one_div_lt_one_div_of_lt (denom_pos k)
    (denom_strictMono (Nat.lt_succ_self k))

theorem ratio_small (k : ℕ) : 0 ≤ ratio k ∧ ratio k < 1 := by
  have h0 : ratio 0 = (1 / 48 : ℝ) := by norm_num [ratio, denom]
  have hle : ratio k ≤ 1 / 48 := by
    calc
      ratio k ≤ ratio 0 := ratio_antitone (Nat.zero_le k)
      _ = 1 / 48 := h0
  constructor
  · change 0 ≤ 1 / denom k
    exact le_of_lt (one_div_pos.mpr (denom_pos k))
  · linarith

theorem coeff_succ (n : ℕ) : coeff (n + 1) = coeff n * ratio n := by
  have hfact :
      (2 * (n + 1) + 1).factorial =
        (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
    calc
      (2 * (n + 1) + 1).factorial = ((2 * n + 2) + 1).factorial := by
        congr 1 <;> omega
      _ = (2 * n + 3) * (2 * n + 2).factorial := by
        rw [Nat.factorial_succ] <;> omega
      _ = (2 * n + 3) * ((2 * n + 2) * (2 * n + 1).factorial) := by
        rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega,
          Nat.factorial_succ] <;> ring
      _ = (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by ring
  have hpow : (8 : ℝ) ^ n ≠ 0 := by positivity
  have hfac : (((2 * n + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : (((2 * n + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
  have h3 : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  dsimp [coeff, ratio, denom]
  rw [hfact, pow_succ]
  push_cast
  field_simp [hpow, hfac, h2, h3] <;> ring

theorem coeff_summable : Summable coeff := by
  have hgeo : Summable (fun n : ℕ => (1 / 8 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  apply Summable.of_nonneg_of_le (fun n => le_of_lt (coeff_pos n)) ?_ hgeo
  intro n
  have hfac : (1 : ℝ) ≤ (((2 * n + 1).factorial : ℕ) : ℝ) := by
    have hnat : (1 : ℕ) ≤ (2 * n + 1).factorial :=
      Nat.succ_le_iff.mpr (Nat.factorial_pos _)
    exact_mod_cast hnat
  have heq :
      coeff n = (1 / 8 : ℝ) ^ n / (((2 * n + 1).factorial : ℕ) : ℝ) := by
    simp only [coeff, one_div, inv_pow, div_eq_mul_inv, mul_inv_rev]
    simp only [one_div]
    ring
  rw [heq]
  exact div_le_self (by positivity) hfac

/-- Corollary 2.2 for every N. Strict on *both* sides; the second
strictness exploits strict decrease of the successive factorial ratios. -/
theorem rational_tail_bound (N : ℕ) :
    prefixSum N < (∑' n, coeff n) ∧
      (∑' n, coeff n) <
        prefixSum N + coeff (N + 1) / (1 - ratio (N + 1)) := by
  let k : ℕ := N + 1
  have hsmall := ratio_small k
  have hstep : ∀ n, k ≤ n → coeff (n + 1) ≤ ratio k * coeff n := by
    intro n hkn
    rw [coeff_succ]
    have hr := ratio_antitone hkn
    calc
      coeff n * ratio n ≤ coeff n * ratio k :=
        mul_le_mul_of_nonneg_left hr (le_of_lt (coeff_pos n))
      _ = ratio k * coeff n := mul_comm _ _
  have hstrict : coeff (k + 2) < ratio k * coeff (k + 1) := by
    have hsucc := coeff_succ (k + 1)
    have hr := ratio_strict_anti_step k
    calc
      coeff (k + 2) = coeff (k + 1) * ratio (k + 1) := by
        convert hsucc using 1 <;> congr 1 <;> omega
      _ < coeff (k + 1) * ratio k :=
        mul_lt_mul_of_pos_left hr (coeff_pos _)
      _ = ratio k * coeff (k + 1) := mul_comm _ _
  have h := V14119Tail.positive_series_tail_strict coeff k (ratio k)
    coeff_pos coeff_summable hsmall.1 hsmall.2 hstep hstrict
  simpa [prefixSum, k] using h

#print axioms SpecialImaginaryPoint.V14119Cor22.coeff_pos
#print axioms SpecialImaginaryPoint.V14119Cor22.denom_strictMono
#print axioms SpecialImaginaryPoint.V14119Cor22.ratio_antitone
#print axioms SpecialImaginaryPoint.V14119Cor22.ratio_strict_anti_step
#print axioms SpecialImaginaryPoint.V14119Cor22.ratio_small
#print axioms SpecialImaginaryPoint.V14119Cor22.coeff_succ
#print axioms SpecialImaginaryPoint.V14119Cor22.coeff_summable
#print axioms SpecialImaginaryPoint.V14119Cor22.rational_tail_bound

end SpecialImaginaryPoint.V14119Cor22
