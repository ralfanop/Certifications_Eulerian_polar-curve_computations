import Mathlib

/-! Exact convergent zeta moments and a summable Taylor majorant for the
diagonal test model of PR #376. No identification with a physical operator
or with an infinite determinant is asserted in this module. -/
namespace SharedCore.Det4Zeta

noncomputable def zetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) ^ s
noncomputable def zetaSeries (s : ℝ) : ℝ := ∑' n : ℕ, zetaTerm s n
noncomputable def spectralTerm (s : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) * ((n : ℝ) + 2)) / ((n : ℝ) + 2) ^ s
noncomputable def moment (s : ℝ) : ℝ := ∑' n : ℕ, spectralTerm s n

theorem zeta_term_summable (s : ℝ) (hs : 1 < s) : Summable (zetaTerm s) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 s).mpr hs
  convert h using 1
  funext n
  unfold zetaTerm
  rw [abs_of_nonneg (by positivity)]

theorem zeta_shifted_sum (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ s) = zetaSeries s - 1 := by
  have h := (zeta_term_summable s hs).tsum_eq_zero_add
  unfold zetaSeries
  have he : (fun n : ℕ => zetaTerm s (n + 1)) =
      (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ s) := by
    funext n
    unfold zetaTerm
    push_cast
    congr 1 <;> congr 1 <;> ring
  rw [he] at h
  have h0 : zetaTerm s 0 = 1 := by simp [zetaTerm]
  rw [h0] at h
  linarith

theorem spectral_term_difference (s : ℝ) (n : ℕ) :
    spectralTerm s n = 1 / ((n : ℝ) + 2) ^ (s - 2) -
      1 / ((n : ℝ) + 2) ^ (s - 1) := by
  unfold spectralTerm
  have ha : 0 < (n : ℝ) + 2 := by positivity
  have ha0 : (n : ℝ) + 2 ≠ 0 := ne_of_gt ha
  have hp : ((n : ℝ) + 2) ^ (s - 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  have h1 : ((n : ℝ) + 2) ^ (s - 1) =
      ((n : ℝ) + 2) ^ (s - 2) * ((n : ℝ) + 2) := by
    calc
      _ = ((n : ℝ) + 2) ^ ((s - 2) + 1) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add ha, Real.rpow_one]
  have h2 : ((n : ℝ) + 2) ^ s =
      ((n : ℝ) + 2) ^ (s - 2) * ((n : ℝ) + 2) ^ (2 : ℕ) := by
    calc
      _ = ((n : ℝ) + 2) ^ ((s - 2) + 2) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add ha, Real.rpow_two]
  rw [h1, h2]
  field_simp <;> ring

theorem spectral_term_nonneg (s : ℝ) (n : ℕ) : 0 ≤ spectralTerm s n := by
  unfold spectralTerm
  positivity

private theorem shifted_summable (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ s) := by
  have h := (Real.summable_one_div_nat_add_rpow 2 s).mpr hs
  convert h using 1
  funext n
  rw [abs_of_nonneg (by positivity)]

theorem spectral_term_summable (s : ℝ) (hs : 3 < s) : Summable (spectralTerm s) := by
  have h := (shifted_summable (s-2) (by linarith)).sub
    (shifted_summable (s-1) (by linarith))
  convert h using 1
  funext n
  exact spectral_term_difference s n

theorem moment_zeta_difference (s : ℝ) (hs : 3 < s) :
    moment s = zetaSeries (s - 2) - zetaSeries (s - 1) := by
  unfold moment
  simp_rw [spectral_term_difference]
  rw [(shifted_summable (s-2) (by linarith)).tsum_sub
    (shifted_summable (s-1) (by linarith)),
    zeta_shifted_sum (s-2) (by linarith), zeta_shifted_sum (s-1) (by linarith)]
  ring

theorem real_zeta_series_eq_riemannZeta (s : ℝ) (hs : 1 < s) :
    (zetaSeries s : ℂ) = riemannZeta (s : ℂ) := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
  unfold zetaSeries
  rw [Complex.ofReal_tsum]
  congr 1
  funext n
  unfold zetaTerm
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity),
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]

theorem moment_riemannZeta_difference (s : ℝ) (hs : 3 < s) :
    (moment s : ℂ) = riemannZeta ((s-2 : ℝ) : ℂ) - riemannZeta ((s-1 : ℝ) : ℂ) := by
  rw [moment_zeta_difference s hs, Complex.ofReal_sub,
    real_zeta_series_eq_riemannZeta (s-2) (by linarith),
    real_zeta_series_eq_riemannZeta (s-1) (by linarith)]

theorem moment_positive (s : ℝ) (hs : 3 < s) : 0 < moment s := by
  unfold moment
  exact (spectral_term_summable s hs).tsum_pos (spectral_term_nonneg s) 0 (by
    unfold spectralTerm
    positivity)

noncomputable def fourthShell (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) / ((n : ℝ) + 2) ^ 3
noncomputable def powerShell (k n : ℕ) : ℝ :=
  fourthShell n * (1 / ((n : ℝ) + 2)) ^ k
noncomputable def powerMoment (k : ℕ) : ℝ := ∑' n : ℕ, powerShell k n

private theorem fourth_shell_eq (n : ℕ) : fourthShell n = spectralTerm 4 n := by
  unfold fourthShell spectralTerm
  rw [show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
  have h : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp <;> ring

theorem fourth_shell_summable : Summable fourthShell := by
  convert spectral_term_summable 4 (by norm_num : (3 : ℝ) < 4) using 1
  funext n
  exact fourth_shell_eq n

private theorem power_shell_nonneg (k n : ℕ) : 0 ≤ powerShell k n := by
  unfold powerShell fourthShell
  positivity

theorem power_shell_le_geometric (k n : ℕ) :
    powerShell k n ≤ (1/2 : ℝ)^k * fourthShell n := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hb : 1 / ((n : ℝ) + 2) ≤ (1/2 : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    linarith
  unfold powerShell
  rw [mul_comm ((1/2 : ℝ)^k)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb k)
    (by unfold fourthShell; positivity)

theorem power_shell_summable (k : ℕ) : Summable (powerShell k) := by
  exact Summable.of_nonneg_of_le (power_shell_nonneg k) (power_shell_le_geometric k)
    (fourth_shell_summable.mul_left ((1/2 : ℝ)^k))

theorem power_moment_le_geometric (k : ℕ) :
    powerMoment k ≤ (1/2 : ℝ)^k * (∑' n : ℕ, fourthShell n) := by
  unfold powerMoment
  rw [← tsum_mul_left]
  exact (power_shell_summable k).tsum_le_tsum (power_shell_le_geometric k)
    (fourth_shell_summable.mul_left ((1/2 : ℝ)^k))

theorem power_moment_nonneg (k : ℕ) : 0 ≤ powerMoment k := by
  unfold powerMoment
  exact tsum_nonneg (power_shell_nonneg k)

theorem fourth_moment_identification : (∑' n : ℕ, fourthShell n) = moment 4 := by
  unfold moment
  exact tsum_congr fourth_shell_eq

noncomputable def taylorMajorant (r : ℝ) (k : ℕ) : ℝ :=
  r ^ (k+4) * powerMoment k / ((k : ℝ)+4)

private theorem taylor_nonneg (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    0 ≤ taylorMajorant r k := by
  unfold taylorMajorant
  exact div_nonneg (mul_nonneg (pow_nonneg hr _) (power_moment_nonneg k)) (by positivity)

theorem taylor_term_le_geometric (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    taylorMajorant r k ≤ (r^4 * moment 4 / 4) * (r/2)^k := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hm := power_moment_le_geometric k
  rw [fourth_moment_identification] at hm
  have hA : 0 ≤ moment 4 := (moment_positive 4 (by norm_num)).le
  have hnum : 0 ≤ r^(k+4) * ((1/2 : ℝ)^k * moment 4) := by positivity
  unfold taylorMajorant
  calc
    _ ≤ r^(k+4) * ((1/2 : ℝ)^k * moment 4) / ((k : ℝ)+4) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (pow_nonneg hr _)) (by positivity)
    _ ≤ r^(k+4) * ((1/2 : ℝ)^k * moment 4) / 4 := by
      apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
      nlinarith
    _ = _ := by rw [pow_add, div_pow]; ring

theorem taylor_majorant_summable (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 2) :
    Summable (taylorMajorant r) := by
  have hg : Summable (fun k : ℕ => (r/2)^k) :=
    summable_geometric_of_lt_one (by positivity) (by linarith)
  exact Summable.of_nonneg_of_le (taylor_nonneg r hr) (taylor_term_le_geometric r hr)
    (hg.mul_left (r^4 * moment 4 / 4))

theorem taylor_majorant_bound (r : ℝ) (hr : 0 ≤ r) (hr2 : r < 2) :
    (∑' k : ℕ, taylorMajorant r k) ≤ (r^4 * moment 4 / 4) / (1-r/2) := by
  have hg : Summable (fun k : ℕ => (r/2)^k) :=
    summable_geometric_of_lt_one (by positivity) (by linarith)
  calc
    _ ≤ ∑' k : ℕ, (r^4 * moment 4 / 4) * (r/2)^k :=
      (taylor_majorant_summable r hr hr2).tsum_le_tsum (taylor_term_le_geometric r hr)
        (hg.mul_left _)
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by rw [abs_of_nonneg (by positivity)]; linarith)]
      ring

end SharedCore.Det4Zeta

#print axioms SharedCore.Det4Zeta.zeta_term_summable
#print axioms SharedCore.Det4Zeta.zeta_shifted_sum
#print axioms SharedCore.Det4Zeta.spectral_term_difference
#print axioms SharedCore.Det4Zeta.spectral_term_nonneg
#print axioms SharedCore.Det4Zeta.spectral_term_summable
#print axioms SharedCore.Det4Zeta.moment_zeta_difference
#print axioms SharedCore.Det4Zeta.real_zeta_series_eq_riemannZeta
#print axioms SharedCore.Det4Zeta.moment_riemannZeta_difference
#print axioms SharedCore.Det4Zeta.moment_positive
#print axioms SharedCore.Det4Zeta.fourth_shell_summable
#print axioms SharedCore.Det4Zeta.power_shell_le_geometric
#print axioms SharedCore.Det4Zeta.power_shell_summable
#print axioms SharedCore.Det4Zeta.power_moment_le_geometric
#print axioms SharedCore.Det4Zeta.power_moment_nonneg
#print axioms SharedCore.Det4Zeta.fourth_moment_identification
#print axioms SharedCore.Det4Zeta.taylor_term_le_geometric
#print axioms SharedCore.Det4Zeta.taylor_majorant_summable
#print axioms SharedCore.Det4Zeta.taylor_majorant_bound
