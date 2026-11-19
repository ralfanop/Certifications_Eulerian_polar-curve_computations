import SpecialImaginaryPoint.V14119DominantPoleQuarticE6

/-! Exact real slope normalization of the M14 §8.5 quartic.
This proves a local bijective real chart, not the complex analytic E6
equivalence or an assertion about the projective normalization globally. -/
noncomputable section
namespace Manuscript14.QuarticE6

def paramU (t : ℝ) : ℝ := t^3 / D t
def paramV (t : ℝ) : ℝ := -t^4 / D t

theorem slope_identity (u v : ℝ) (hu : u ≠ 0) :
    Q u v = u^3 * (u * D (-v/u) - (-v/u)^3) := by
  unfold Q D
  field_simp [hu] <;> ring

theorem slope_relation (u v : ℝ) (hu : u ≠ 0) (hq : Q u v = 0) :
    u * D (-v/u) = (-v/u)^3 := by
  have h := slope_identity u v hu
  rw [hq] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ hu))

theorem slope_D_ne (u v : ℝ) (hu : u ≠ 0) (hq : Q u v = 0) :
    D (-v/u) ≠ 0 := by
  intro hd
  have h := slope_relation u v hu hq
  rw [hd, mul_zero] at h
  have ht : -v/u = 0 := by
    by_contra hn
    exact pow_ne_zero 3 hn h.symm
  rw [ht] at hd
  norm_num [D] at hd

theorem reconstruct_of_curve (u v : ℝ) (hu : u ≠ 0) (hq : Q u v = 0) :
    paramU (-v/u) = u ∧ paramV (-v/u) = v := by
  have hd := slope_D_ne u v hu hq
  have he := slope_relation u v hu hq
  have ht : (-v/u)*u = -v := by field_simp [hu]
  constructor
  · unfold paramU
    exact (div_eq_iff hd).2 he.symm
  · unfold paramV
    apply (div_eq_iff hd).2
    calc
      -(-v/u)^4 = -(-v/u) * (-v/u)^3 := by ring
      _ = -(-v/u) * (u * D (-v/u)) := by rw [← he]
      _ = -((-v/u)*u) * D (-v/u) := by ring
      _ = v * D (-v/u) := by rw [ht]; ring

theorem zero_axis (v : ℝ) : Q 0 v = 0 ↔ v = 0 ∨ v = -32 := by
  have he : Q 0 v = v^3*(v/32+1) := by unfold Q; ring
  rw [he, mul_eq_zero]
  constructor
  · rintro (h | h)
    · left
      by_contra hn
      exact pow_ne_zero 3 hn h
    · right; linarith
  · rintro (h | h)
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num

theorem slope_of_param (t : ℝ) (ht : t ≠ 0) (hd : D t ≠ 0) :
    -paramV t / paramU t = t := by
  unfold paramU paramV
  field_simp [ht, hd] <;> ring

theorem param_injective (s t : ℝ) (hs : D s ≠ 0) (ht : D t ≠ 0)
    (hu : paramU s = paramU t) (hv : paramV s = paramV t) : s = t := by
  by_cases h0 : s = 0
  · subst s
    have hz : paramU t = 0 := by simpa [paramU, D] using hu.symm
    have ht0 : t = 0 := by
      by_contra hn
      exact div_ne_zero (pow_ne_zero 3 hn) ht hz
    exact ht0.symm
  · have ht0 : t ≠ 0 := by
      intro h
      subst t
      have hz : paramU s = 0 := by simpa [paramU, D] using hu
      exact div_ne_zero (pow_ne_zero 3 h0) hs hz
    calc
      s = -paramV s / paramU s := (slope_of_param s h0 hs).symm
      _ = -paramV t / paramU t := by rw [hu, hv]
      _ = t := slope_of_param t ht0 ht

theorem large_slope_denominator (t : ℝ) (h : 1 ≤ |t|) :
    |D t| ≤ 2*t^4 := by
  have ha : 1 ≤ t^2 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg t]
  have hb : t^2 ≤ t^4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sq_nonneg t)]
  unfold D
  apply abs_le.mpr
  constructor <;> nlinarith

theorem slope_small (u v : ℝ) (hu : u ≠ 0) (hq : Q u v = 0)
    (hv : |v| < 1/2) : |-v/u| < 1 := by
  let t : ℝ := -v/u
  change |t| < 1
  by_contra hn
  have ht : 1 ≤ |t| := le_of_not_gt hn
  have hD : D t ≠ 0 := slope_D_ne u v hu hq
  have he : paramV t = v := (reconstruct_of_curve u v hu hq).2
  have hm : -t^4 = v * D t := (div_eq_iff hD).1 he
  have ha : t^4 = |v| * |D t| := by
    have h := congrArg abs hm
    rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ t^4), abs_mul] at h
    exact h
  have hp : 0 < t^4 := by
    have h2 : 1 ≤ t^2 := by rw [← sq_abs]; nlinarith [abs_nonneg t]
    nlinarith [sq_nonneg (t^2 - 1)]
  have hh := mul_le_mul_of_nonneg_left (large_slope_denominator t ht) (abs_nonneg v)
  have hlt := mul_lt_mul_of_pos_right hv (show 0 < 2*t^4 by positivity)
  linarith

/-- Every real point in the horizontal strip has a unique small real slope
parameter. The singular origin is included, and the other axis point excluded. -/
theorem local_real_chart (u v : ℝ) (hq : Q u v = 0) (hv : |v| < 1/2) :
    ∃! t : ℝ, |t| < 1 ∧ paramU t = u ∧ paramV t = v := by
  have hd (t : ℝ) (ht : |t| < 1) : D t ≠ 0 := by
    have h := denominator_near_origin t ht.le
    linarith
  by_cases hu : u = 0
  · subst u
    have hv0 : v = 0 := by
      rcases (zero_axis v).1 hq with h | h
      · exact h
      · rw [h] at hv
        norm_num at hv
    subst v
    have hU : paramU 0 = 0 := by norm_num [paramU,D]
    have hV : paramV 0 = 0 := by norm_num [paramV,D]
    refine ⟨0, ⟨by norm_num, hU, hV⟩, ?_⟩
    intro y hy
    exact param_injective y 0 (hd y hy.1) (by norm_num [D])
      (hy.2.1.trans hU.symm) (hy.2.2.trans hV.symm)
  · have h := slope_small u v hu hq hv
    have hr := reconstruct_of_curve u v hu hq
    refine ⟨-v/u, ⟨h, hr.1, hr.2⟩, ?_⟩
    intro y hy
    exact param_injective y (-v/u) (hd y hy.1) (hd _ h)
      (hy.2.1.trans hr.1.symm) (hy.2.2.trans hr.2.symm)

theorem param_continuity_at_origin :
    ContinuousAt paramU 0 ∧ ContinuousAt paramV 0 := by
  unfold paramU paramV
  have hD : ContinuousAt D 0 := by unfold D; fun_prop
  have hz : D 0 ≠ 0 := by norm_num [D]
  constructor
  · exact (continuousAt_id.pow 3).div hD hz
  · exact (continuousAt_id.pow 4).neg.div hD hz

#print axioms slope_identity
#print axioms slope_relation
#print axioms slope_D_ne
#print axioms reconstruct_of_curve
#print axioms zero_axis
#print axioms slope_of_param
#print axioms param_injective
#print axioms large_slope_denominator
#print axioms slope_small
#print axioms local_real_chart
#print axioms param_continuity_at_origin
end Manuscript14.QuarticE6
