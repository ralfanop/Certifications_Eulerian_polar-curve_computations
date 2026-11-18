import Mathlib

/-! Scalar spectral-shell criterion for the diagonal model in PR #373.
This proves the exact real-exponent summability threshold, not an
operator-domain or singular-value identification on a Hilbert space. -/

namespace SharedCore.SchattenFredholm

noncomputable def realPSeries (p : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 2) ^ (p - 2)

noncomputable def realShell (p : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) / ((n : ℝ) + 2)) * realPSeries p n

theorem real_pseries_nonneg (p : ℝ) (n : ℕ) : 0 ≤ realPSeries p n := by
  unfold realPSeries
  positivity

theorem real_shell_factor_lower (n : ℕ) :
    (1 / 2 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  apply (le_div_iff₀ (by positivity)).2
  linarith

theorem real_shell_factor_upper (n : ℕ) :
    ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ 1 := by
  apply (div_le_iff₀ (by positivity)).2
  linarith

theorem real_shell_nonneg (p : ℝ) (n : ℕ) : 0 ≤ realShell p n := by
  unfold realShell
  exact mul_nonneg (by positivity) (real_pseries_nonneg p n)

theorem real_shell_le_pseries (p : ℝ) (n : ℕ) :
    realShell p n ≤ realPSeries p n := by
  unfold realShell
  calc
    _ ≤ 1 * realPSeries p n :=
      mul_le_mul_of_nonneg_right (real_shell_factor_upper n) (real_pseries_nonneg p n)
    _ = _ := one_mul _

theorem real_pseries_le_twice_shell (p : ℝ) (n : ℕ) :
    realPSeries p n ≤ 2 * realShell p n := by
  have h := mul_le_mul_of_nonneg_right (real_shell_factor_lower n) (real_pseries_nonneg p n)
  unfold realShell
  linarith

theorem real_pseries_summable_iff (p : ℝ) :
    Summable (realPSeries p) ↔ 3 < p := by
  have he : realPSeries p = (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (p - 2)) := by
    funext n
    unfold realPSeries
    rw [abs_of_nonneg (by positivity)]
  rw [he, Real.summable_one_div_nat_add_rpow 2 (p - 2)]
  constructor <;> intro h <;> linarith

theorem real_shell_summable_iff (p : ℝ) :
    Summable (realShell p) ↔ 3 < p := by
  constructor
  · intro h
    have hlarge : Summable (fun n : ℕ => 2 * realShell p n) := h.mul_left 2
    exact (real_pseries_summable_iff p).mp
      (Summable.of_nonneg_of_le (real_pseries_nonneg p) (real_pseries_le_twice_shell p) hlarge)
  · intro h
    exact Summable.of_nonneg_of_le (real_shell_nonneg p) (real_shell_le_pseries p)
      ((real_pseries_summable_iff p).mpr h)

theorem real_shell_eq_spectral_moment (p : ℝ) (n : ℕ) :
    realShell p n = (((n : ℝ) + 1) * ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ p := by
  unfold realShell realPSeries
  have ha : 0 < (n : ℝ) + 2 := by positivity
  have hne : (n : ℝ) + 2 ≠ 0 := ne_of_gt ha
  have hpow : ((n : ℝ) + 2) ^ (p - 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  have he : ((n : ℝ) + 2) ^ p = ((n : ℝ) + 2) ^ (p - 2) * ((n : ℝ) + 2) ^ (2 : ℕ) := by
    calc
      _ = ((n : ℝ) + 2) ^ ((p - 2) + 2) := by congr 1 <;> ring
      _ = ((n : ℝ) + 2) ^ (p - 2) * ((n : ℝ) + 2) ^ (2 : ℝ) := Real.rpow_add ha _ _
      _ = _ := by rw [Real.rpow_two]
  rw [he]
  field_simp <;> ring

theorem real_spectral_moment_summable_iff (p : ℝ) :
    Summable (fun n : ℕ => (((n : ℝ) + 1) * ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ p) ↔ 3 < p := by
  have he : (fun n : ℕ => (((n : ℝ) + 1) * ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ p) = realShell p :=
    funext fun n => (real_shell_eq_spectral_moment p n).symm
  rw [he, real_shell_summable_iff]

end SharedCore.SchattenFredholm

#print axioms SharedCore.SchattenFredholm.real_pseries_nonneg
#print axioms SharedCore.SchattenFredholm.real_shell_factor_lower
#print axioms SharedCore.SchattenFredholm.real_shell_factor_upper
#print axioms SharedCore.SchattenFredholm.real_shell_nonneg
#print axioms SharedCore.SchattenFredholm.real_shell_le_pseries
#print axioms SharedCore.SchattenFredholm.real_pseries_le_twice_shell
#print axioms SharedCore.SchattenFredholm.real_pseries_summable_iff
#print axioms SharedCore.SchattenFredholm.real_shell_summable_iff
#print axioms SharedCore.SchattenFredholm.real_shell_eq_spectral_moment
#print axioms SharedCore.SchattenFredholm.real_spectral_moment_summable_iff
