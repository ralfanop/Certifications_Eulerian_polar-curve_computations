import SpecialImaginaryPoint.EulerianLegendreQuarticJet
import SpecialImaginaryPoint.EulerianLegendreSupport
import Mathlib.Analysis.Calculus.Taylor

namespace M14.EulerianLegendre
noncomputable section

theorem profile_even (x : ℝ) : profile (-x) = profile x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp [profile, hx, Real.sinh_neg]

theorem cumulant_even (x : ℝ) : cumulant (-x) = cumulant x := by
  simp only [cumulant, profile_even]

theorem langevin_odd (x : ℝ) : langevin (-x) = -langevin x := by
  by_cases hx : x = 0
  · simp [hx, langevin]
  · simp [langevin, langevinRaw, hx, Real.sinh_neg, Real.cosh_neg]
    ring

theorem cumulant_contDiff (n : ℕ) : ContDiff ℝ n cumulant := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (cumulant_analytic x).contDiffAt

theorem cumulant_taylor_four (x : ℝ) :
    taylorWithinEval cumulant 4 (Set.Icc (0 : ℝ) 1) 0 x =
      x^2 / 6 - x^4 / 180 := by
  have hd (k : ℕ) : iteratedDerivWithin k cumulant (Set.Icc (0 : ℝ) 1) 0 =
      iteratedDeriv k cumulant 0 :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1))
      (cumulant_contDiff k).contDiffAt (by norm_num)
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hd, iteratedDeriv_succ,
    iteratedDeriv_zero, cumulant_zero, cumulant_first_deriv_zero,
    cumulant_second_deriv_zero, cumulant_third_deriv_zero, cumulant_fourth_deriv_zero]
  norm_num [Nat.factorial, smul_eq_mul]
  <;> ring

theorem cumulant_fifth_deriv_zero :
    deriv (deriv (deriv (deriv (deriv cumulant)))) 0 = 0 := by
  have evenD (f : ℝ → ℝ) (he : ∀ x, f (-x) = f x)
      (hf : ∀ x, DifferentiableAt ℝ f x) :
      ∀ x, deriv f (-x) = -deriv f x := by
    intro x
    have h := ((hf (-x)).hasDerivAt.comp x (hasDerivAt_id x).neg)
    have h' : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * -1) x := by
      change HasDerivAt (fun y : ℝ => f (-y)) _ x at h
      simpa only [smul_eq_mul, mul_neg, mul_one, neg_mul, one_mul] using h
    have hfun : (fun y : ℝ => f (-y)) = f := funext he
    rw [hfun] at h'
    linarith [h'.unique (hf x).hasDerivAt]
  have oddD (f : ℝ → ℝ) (he : ∀ x, f (-x) = -f x)
      (hf : ∀ x, DifferentiableAt ℝ f x) :
      ∀ x, deriv f (-x) = deriv f x := by
    intro x
    have h := ((hf (-x)).hasDerivAt.comp x (hasDerivAt_id x).neg)
    have h' : HasDerivAt (fun y : ℝ => f (-y)) (deriv f (-x) * -1) x := by
      change HasDerivAt (fun y : ℝ => f (-y)) _ x at h
      simpa only [smul_eq_mul, mul_neg, mul_one, neg_mul, one_mul] using h
    have hfun : (fun y : ℝ => f (-y)) = (fun y : ℝ => -f y) := funext he
    rw [hfun] at h'
    have hn : HasDerivAt (fun y : ℝ => -f y) (-deriv f x) x := (hf x).hasDerivAt.neg
    linarith [h'.unique hn]
  have h1 := evenD cumulant cumulant_even (fun x => (cumulant_analytic x).differentiableAt)
  have h2 := oddD (deriv cumulant) h1 (fun x => (cumulant_analytic x).deriv.differentiableAt)
  have h3 := evenD (deriv (deriv cumulant)) h2 (fun x => (cumulant_analytic x).deriv.deriv.differentiableAt)
  have h4 := oddD (deriv (deriv (deriv cumulant))) h3 (fun x => (cumulant_analytic x).deriv.deriv.deriv.differentiableAt)
  have h5 := evenD (deriv (deriv (deriv (deriv cumulant)))) h4
    (fun x => (cumulant_analytic x).deriv.deriv.deriv.deriv.differentiableAt) 0
  simp only [neg_zero] at h5
  linarith

theorem cumulant_taylor_five (x : ℝ) :
    taylorWithinEval cumulant 5 (Set.Icc (0 : ℝ) 1) 0 x =
      x^2 / 6 - x^4 / 180 := by
  have hd : iteratedDerivWithin 5 cumulant (Set.Icc (0 : ℝ) 1) 0 = 0 := by
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0:ℝ) < 1))
      (cumulant_contDiff 5).contDiffAt (by norm_num)]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using cumulant_fifth_deriv_zero
  rw [taylorWithinEval_succ, cumulant_taylor_four, hd]
  simp

theorem cumulant_order_six_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |x| ≤ 1 →
      |cumulant x - (x^2 / 6 - x^4 / 180)| ≤ C * |x|^6 := by
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := cumulant) (n := 5) (a := 0) (b := 1) (by norm_num)
    (cumulant_contDiff 6).contDiffOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have hmem : |x| ∈ Set.Icc (0 : ℝ) 1 := ⟨abs_nonneg _, hx⟩
  have h := hC |x| hmem
  rw [cumulant_taylor_five, Real.norm_eq_abs, sub_zero] at h
  have he : cumulant |x| = cumulant x := by
    rcases le_or_gt 0 x with hx' | hx'
    · rw [abs_of_nonneg hx']
    · rw [abs_of_neg hx', cumulant_even]
  have h2 : |x|^2 = x^2 := by rw [← abs_pow]; exact abs_of_nonneg (sq_nonneg x)
  have h4 : |x|^4 = x^4 := by calc
    |x|^4 = (|x|^2)^2 := by ring
    _ = x^4 := by rw [h2]; ring
  rw [he, h2, h4] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (abs_nonneg _) _))

end
end M14.EulerianLegendre

#print axioms M14.EulerianLegendre.profile_even
#print axioms M14.EulerianLegendre.cumulant_even
#print axioms M14.EulerianLegendre.langevin_odd
#print axioms M14.EulerianLegendre.cumulant_contDiff
#print axioms M14.EulerianLegendre.cumulant_taylor_four
#print axioms M14.EulerianLegendre.cumulant_fifth_deriv_zero
#print axioms M14.EulerianLegendre.cumulant_taylor_five
#print axioms M14.EulerianLegendre.cumulant_order_six_bound
