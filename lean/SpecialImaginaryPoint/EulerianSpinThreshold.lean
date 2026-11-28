import SpecialImaginaryPoint.EulerianLangevinRange
namespace M14.EulerianSpin
open M14.EulerianLegendre
noncomputable section

def critical (eta : ℝ) : ℝ := 2 * inverseLangevin (1 / eta)
def target (eta H : ℝ) : ℝ := eta * langevin (H/2)

theorem critical_exact (eta : ℝ) (he : 1 < eta) :
    langevin (critical eta / 2) = 1 / eta := by
  have hp : 0 < eta := by linarith
  have hq : 0 < 1 / eta := by positivity
  have hq1 : 1 / eta < 1 := (div_lt_iff₀ hp).2 (by linarith)
  have hmem : 1 / eta ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith,hq1⟩
  have h := inverseLangevin_right_on_interval (1/eta) hmem
  simpa [critical] using h

theorem critical_pos (eta : ℝ) (he : 1 < eta) : 0 < critical eta := by
  have h := critical_exact eta he
  have hp : 0 < 1 / eta := by positivity
  by_contra! hn
  have hm := langevin_strictMono.monotone (show critical eta / 2 ≤ 0 by linarith)
  rw [h] at hm
  simp [langevin] at hm
  linarith

theorem threshold_exact (eta : ℝ) (he : 1 < eta) : target eta (critical eta) = 1 := by
  unfold target
  rw [critical_exact eta he]
  field_simp [show eta ≠ 0 by linarith]

theorem target_strictMono (eta : ℝ) (he : 0 < eta) : StrictMono (target eta) := by
  intro a b hab
  exact mul_lt_mul_of_pos_left (langevin_strictMono (show a/2 < b/2 by linarith)) he

theorem critical_unique (eta : ℝ) (he : 1 < eta) :
    ∃! H : ℝ, target eta H = 1 := by
  refine ⟨critical eta, threshold_exact eta he, ?_⟩
  intro H h
  apply (target_strictMono eta (by linarith)).injective
  rw [h,threshold_exact eta he]

theorem subcritical_iff (eta H : ℝ) (he : 1 < eta) :
    target eta H < 1 ↔ H < critical eta := by
  rw [← threshold_exact eta he]
  exact (target_strictMono eta (by linarith)).lt_iff_lt

theorem critical_antitone (a b : ℝ) (ha : 1 < a) (hab : a < b) :
    critical b < critical a := by
  have hb : 1 < b := lt_trans ha hab
  have h : 1/b < 1/a := one_div_lt_one_div_of_lt (by linarith) hab
  have hL : langevin (critical b/2) < langevin (critical a/2) := by
    rw [critical_exact b hb,critical_exact a ha]
    exact h
  have hh := langevin_strictMono.lt_iff_lt.mp hL
  linarith

def spinRatio (j : ℝ) : ℝ := Real.sqrt ((j+1)/j)
def spinCritical (j : ℝ) : ℝ := critical (spinRatio j)

theorem spinRatio_gt_one (j : ℝ) (hj : 0 < j) : 1 < spinRatio j := by
  have h : 1 < (j+1)/j := (lt_div_iff₀ hj).2 (by linarith)
  have hs : (spinRatio j)^2 = (j+1)/j := Real.sq_sqrt (by linarith)
  have hn : 0 ≤ spinRatio j := Real.sqrt_nonneg _
  by_contra! hh
  nlinarith [mul_nonneg hn (sub_nonneg.mpr hh)]

theorem spinRatio_decreasing (j k : ℝ) (hj : 0 < j) (hjk : j < k) :
    spinRatio k < spinRatio j := by
  have hk : 0 < k := lt_trans hj hjk
  have h : 1/k < 1/j := one_div_lt_one_div_of_lt hj hjk
  have h1 : (k+1)/k = 1+1/k := by field_simp [hk.ne'] <;> ring
  have h2 : (j+1)/j = 1+1/j := by field_simp [hj.ne'] <;> ring
  unfold spinRatio
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [h1,h2]
  linarith

theorem spinCritical_increasing (j k : ℝ) (hj : 0 < j) (hjk : j < k) :
    spinCritical j < spinCritical k := by
  exact critical_antitone (spinRatio k) (spinRatio j)
    (spinRatio_gt_one k (lt_trans hj hjk)) (spinRatio_decreasing j k hj hjk)

/-- Algebraic classical reference for the large-spin asymptotics. -/
theorem spin_reference_exact (j : ℝ) (hj : 0 < j) :
    2 / (1-Real.sqrt (j/(j+1))) = 2*(j+1+Real.sqrt (j*(j+1))) := by
  have hp : 0 < j+1 := by positivity
  let u := Real.sqrt (j/(j+1))
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u^2 = j/(j+1) := Real.sq_sqrt (by positivity)
  have hlt : j/(j+1) < 1 := (div_lt_iff₀ hp).2 (by linarith)
  have hu1 : u < 1 := by
    by_contra! h
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0 ≤ u+1 by linarith)]
  have hv : Real.sqrt (j*(j+1)) = (j+1)*u := by
    rw [show j*(j+1) = (j+1)^2*(j/(j+1)) by field_simp [hp.ne'] <;> ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hp]
  change 2/(1-u) = _
  rw [hv]
  apply (div_eq_iff (sub_ne_zero.mpr (Ne.symm hu1.ne))).2
  have hq : (j+1)*u^2 = j := by rw [hu2]; field_simp [hp.ne']
  nlinarith

#print axioms critical_exact
#print axioms critical_pos
#print axioms threshold_exact
#print axioms target_strictMono
#print axioms critical_unique
#print axioms subcritical_iff
#print axioms critical_antitone
#print axioms spinRatio_gt_one
#print axioms spinRatio_decreasing
#print axioms spinCritical_increasing
#print axioms spin_reference_exact
end
end M14.EulerianSpin
