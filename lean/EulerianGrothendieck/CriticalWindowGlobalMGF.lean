import CriticalWindowQuartic

/-! Actual global deficit of the logarithm of the real uniform MGF.
The normalization here is sinhc(√3 h), so the Gaussian comparison is h²/2. -/
open NormedSpace
namespace M12GlobalMGF

noncomputable def sinhc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sinh x / x

noncomputable def deficitConstant : ℝ := 1 / (180 * Real.exp 24)

theorem sinhc_neg (x : ℝ) : sinhc (-x) = sinhc x := by
  by_cases h : x = 0
  · simp [h, sinhc]
  · simp [sinhc, h, Real.sinh_neg]

theorem sinhc_pos_of_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 < sinhc x := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h, sinhc]
  · rw [sinhc, if_neg h.ne']
    exact div_pos (Real.sinh_pos_iff.mpr h) h

theorem sinh_quartic_gap (x : ℝ) (hx : 0 ≤ x) :
    x^5 / 180 ≤ Real.exp (x^2/6)*x - Real.sinh x := by
  let f : ℕ → ℝ := fun n => x^(2*n+1) / ((2*n+1).factorial : ℝ)
  let g : ℕ → ℝ := fun n => ((x^2/6)^n / (n.factorial : ℝ))*x
  have hf : HasSum f (Real.sinh x) := Real.hasSum_sinh x
  have hg : HasSum g (Real.exp (x^2/6)*x) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (expSeries_div_hasSum_exp ℝ (x^2/6)).mul_right x
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    have hd : (6 : ℝ)^n * (n.factorial : ℝ) ≤ ((2*n+1).factorial : ℝ) := by
      exact_mod_cast M12CriticalWindow.factorial_comparison n
    have hp : (0 : ℝ) < 6^n * (n.factorial : ℝ) := by positivity
    have hdiv : (x^2)^n / ((2*n+1).factorial : ℝ) ≤
        (x^2)^n / (6^n * (n.factorial : ℝ)) :=
      div_le_div_of_nonneg_left (by positivity) hp hd
    calc
      f n = ((x^2)^n / ((2*n+1).factorial : ℝ))*x := by
        simp only [f, pow_succ, pow_mul]
        ring
      _ ≤ ((x^2)^n / (6^n * (n.factorial : ℝ)))*x :=
        mul_le_mul_of_nonneg_right hdiv hx
      _ = g n := by simp only [g, div_pow, div_div]
  have hsum : HasSum (fun n => g n - f n)
      (Real.exp (x^2/6)*x - Real.sinh x) := hg.sub hf
  have hgap := hsum.summable.le_tsum 2 (fun j _ => sub_nonneg.mpr (hfg j))
  rw [hsum.tsum_eq] at hgap
  norm_num [g, f] at hgap
  nlinarith only [hgap]

theorem sinhc_quartic_gap (x : ℝ) (hx : 0 ≤ x) :
    sinhc x ≤ Real.exp (x^2/6)-x^4/180 := by
  rcases eq_or_lt_of_le hx with h | h
  · simp [← h, sinhc]
  · rw [sinhc, if_neg h.ne']
    apply (div_le_iff₀ h).2
    have hg := sinh_quartic_gap x h.le
    nlinarith only [hg]

theorem deficit_compact (x : ℝ) (hx : 0 ≤ x) (hR : x ≤ 12) :
    x^4 / (180 * Real.exp 24) ≤ x^2/6 - Real.log (sinhc x) := by
  have he : 0 < Real.exp (x^2/6) := Real.exp_pos _
  have hm := sinhc_pos_of_nonneg x hx
  have hlog := Real.log_le_sub_one_of_pos (div_pos hm he)
  rw [Real.log_div hm.ne' he.ne', Real.log_exp] at hlog
  have hg := div_le_div_of_nonneg_right (sinhc_quartic_gap x hx) he.le
  rw [sub_div, div_self he.ne', div_div] at hg
  have ht : x^2/6 ≤ 24 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hR)]
  have he' : Real.exp (x^2/6) ≤ Real.exp 24 := Real.exp_le_exp.mpr ht
  have hd : x^4 / (180 * Real.exp 24) ≤ x^4 / (180 * Real.exp (x^2/6)) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left he' (by norm_num))
  linarith only [hlog, hg, hd]

theorem deficit_tail (x : ℝ) (hx : 12 ≤ x) :
    x^2/12 ≤ x^2/6 - Real.log (sinhc x) := by
  have hp : 0 < x := by linarith
  have hm := sinhc_pos_of_nonneg x hp.le
  have hs : Real.sinh x ≤ Real.exp x := by
    rw [Real.sinh_eq]
    linarith [Real.exp_pos x, Real.exp_pos (-x)]
  have hc : sinhc x ≤ Real.exp x := by
    rw [sinhc, if_neg hp.ne']
    apply (div_le_iff₀ hp).2
    have hmul := mul_nonneg (Real.exp_pos x).le (show 0 ≤ x-1 by linarith)
    nlinarith only [hs, hmul]
  have hl : Real.log (sinhc x) ≤ x := (Real.log_le_iff_le_exp hm).2 hc
  nlinarith only [hl, mul_nonneg hp.le (sub_nonneg.mpr hx)]

theorem deficitConstant_pos : 0 < deficitConstant := by
  unfold deficitConstant
  positivity

theorem deficitConstant_le : deficitConstant ≤ 1/12 := by
  unfold deficitConstant
  have he : 1 ≤ Real.exp 24 := by
    simpa only [Real.exp_zero] using
      (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 24 by norm_num))
  apply (div_le_iff₀ (show 0 < 180 * Real.exp 24 by positivity)).2
  linarith

theorem global_deficit_nonneg (x : ℝ) (hx : 0 ≤ x) :
    deficitConstant * min (x^4) (x^2) ≤ x^2/6 - Real.log (sinhc x) := by
  by_cases h : x ≤ 12
  · calc
      deficitConstant * min (x^4) (x^2) ≤ deficitConstant * x^4 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) deficitConstant_pos.le
      _ = x^4 / (180 * Real.exp 24) := by unfold deficitConstant; ring
      _ ≤ _ := deficit_compact x hx h
  · calc
      deficitConstant * min (x^4) (x^2) ≤ deficitConstant * x^2 :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) deficitConstant_pos.le
      _ ≤ (1/12)*x^2 := mul_le_mul_of_nonneg_right deficitConstant_le (sq_nonneg x)
      _ = x^2/12 := by ring
      _ ≤ _ := deficit_tail x (le_of_lt (lt_of_not_ge h))

theorem global_deficit (x : ℝ) :
    deficitConstant * min (x^4) (x^2) ≤ x^2/6 - Real.log (sinhc x) := by
  by_cases hx : 0 ≤ x
  · exact global_deficit_nonneg x hx
  · have ht : 0 ≤ -x := by linarith
    have h := global_deficit_nonneg (-x) ht
    rw [sinhc_neg, show (-x)^4 = x^4 by ring, show (-x)^2 = x^2 by ring] at h
    exact h

theorem standardized_global_deficit (h : ℝ) :
    deficitConstant * min (h^4) (h^2) ≤
      h^2/2 - Real.log (sinhc (Real.sqrt 3 * h)) := by
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have h2 : (Real.sqrt 3 * h)^2 = 3*h^2 := by rw [mul_pow, hs]
  have h4 : (Real.sqrt 3 * h)^4 = 9*h^4 := by
    calc
      (Real.sqrt 3 * h)^4 = ((Real.sqrt 3 * h)^2)^2 := by ring
      _ = 9*h^4 := by rw [h2]; ring
  have hd := global_deficit (Real.sqrt 3 * h)
  rw [h2, h4] at hd
  have hm : min (h^4) (h^2) ≤ min (9*h^4) (3*h^2) :=
    min_le_min (by nlinarith [sq_nonneg (h^2)]) (by nlinarith [sq_nonneg h])
  have hmul := mul_le_mul_of_nonneg_left hm deficitConstant_pos.le
  linarith only [hd, hmul]

end M12GlobalMGF

#print axioms M12GlobalMGF.sinhc_neg
#print axioms M12GlobalMGF.sinh_quartic_gap
#print axioms M12GlobalMGF.sinhc_quartic_gap
#print axioms M12GlobalMGF.deficit_compact
#print axioms M12GlobalMGF.deficit_tail
#print axioms M12GlobalMGF.deficitConstant_pos
#print axioms M12GlobalMGF.global_deficit
#print axioms M12GlobalMGF.standardized_global_deficit
