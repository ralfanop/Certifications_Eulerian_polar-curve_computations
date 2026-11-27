import Manuscript15.DiskFamily20261127

/-! M15 Lemma 8.1: exhaustive equality cases on the closed disk,
including exclusion of interior extremizers and coalescence at threshold.
These statements are CI candidates until the kernel checks them. -/
noncomputable section
open Complex
namespace Manuscript15.DiskFamily20261127

theorem first_min_radius_eq {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hl : r ≤ threshold) (hz : z ∈ disk r)
    (he : ‖1-z^2‖^2=(1+(1-r)^2)^2) : ‖z-I‖=r := by
  let s := ‖z-I‖
  have hs : 0 ≤ s := norm_nonneg _
  have hsr : s ≤ r := disk_radius_bound hz
  by_contra! hn
  have hlt : s < r := lt_of_le_of_ne hsr hn
  have hmem : z ∈ disk s := by
    simp [disk,s,Metric.mem_closedBall,Complex.dist_eq]
  have hmin := disk_first_lower hmem (lt_trans hlt hr2) (le_trans hsr hl)
  have ht : 0 < 1-r := by linarith [threshold_lt_one]
  have hstrict : (1-r)^2 < (1-s)^2 := by
    have hp := mul_pos (show 0 < r-s by linarith) (show 0 < 2-r-s by linarith)
    nlinarith
  have hp := mul_pos (show 0 < (1+(1-s)^2)-(1+(1-r)^2) by linarith)
    (show 0 < (1+(1-s)^2)+(1+(1-r)^2) by positivity)
  nlinarith

theorem second_min_radius_eq {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hz : z ∈ disk r)
    (he : ‖1-z^2‖^2=(2-r^2)^2/2) : ‖z-I‖=r := by
  let s := ‖z-I‖
  have hs : 0 ≤ s := norm_nonneg _
  have hsr : s ≤ r := disk_radius_bound hz
  by_contra! hn
  have hlt : s < r := lt_of_le_of_ne hsr hn
  have hmem : z ∈ disk s := by
    simp [disk,s,Metric.mem_closedBall,Complex.dist_eq]
  have hmin := disk_second_lower hmem (lt_trans hlt hr2)
  have hsq : r^2 < 2 := by
    have hp := mul_pos (sub_pos.mpr hr2) (show 0 < Real.sqrt 2+r by positivity)
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  have hs2 : s^2 < r^2 := by
    have hp := mul_pos (show 0 < r-s by linarith) (show 0 < r+s by linarith)
    nlinarith
  have hp := mul_pos (show 0 < (2-s^2)-(2-r^2) by linarith)
    (show 0 < (2-s^2)+(2-r^2) by linarith)
  nlinarith

theorem first_extremizer_iff {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hl : r ≤ threshold) (hz : z ∈ disk r) :
    ‖1-z^2‖^2=(1+(1-r)^2)^2 ↔ z=firstPoint r := by
  constructor
  · intro he
    have hb := first_min_radius_eq hr hr2 hl hz he
    have hc := boundary_coords z
    rw [hb] at hc
    have hy : 1-r ≤ z.im := by
      have h := Complex.abs_im_le_norm (z-I)
      rw [hb] at h
      simp only [Complex.sub_im,Complex.I_im] at h
      linarith [(abs_le.mp h).1]
    have heq := boundary_polynomial z r hc
    have hyy := first_boundary_unique hr2 hl hy (heq.symm.trans he)
    have hx : z.re=0 := by rw [hyy] at hc; nlinarith
    apply Complex.ext
    · exact hx
    · exact hyy
  · rintro rfl
    exact first_point_value r

theorem second_extremizer_iff {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hl : threshold ≤ r) (hz : z ∈ disk r) :
    ‖1-z^2‖^2=(2-r^2)^2/2 ↔
      z=secondPoint r 1 ∨ z=secondPoint r (-1) := by
  constructor
  · intro he
    have hb := second_min_radius_eq hr hr2 hz he
    have hc := boundary_coords z
    rw [hb] at hc
    have heq := boundary_polynomial z r hc
    have hyy := second_boundary_unique (heq.symm.trans he)
    rw [hyy] at hc
    have hrad : 0 ≤ r^2-(vertex r-1)^2 := by nlinarith [sq_nonneg z.re]
    have hs := Real.sq_sqrt hrad
    have hprod : (z.re-Real.sqrt (r^2-(vertex r-1)^2))*
        (z.re+Real.sqrt (r^2-(vertex r-1)^2))=0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left
      apply Complex.ext
      · change z.re = 1*Real.sqrt (r^2-(vertex r-1)^2)
        linarith
      · exact hyy
    · right
      apply Complex.ext
      · change z.re = (-1)*Real.sqrt (r^2-(vertex r-1)^2)
        linarith
      · exact hyy
  · rintro (rfl | rfl)
    · exact second_point_value hr hr2 hl (by norm_num : (1:ℝ)^2=1)
    · exact second_point_value hr hr2 hl (by norm_num : (-1:ℝ)^2=1)

theorem threshold_vertex : vertex threshold=1-threshold := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold vertex threshold
  nlinarith

theorem threshold_coalescence (sgn : ℝ) :
    secondPoint threshold sgn=firstPoint threshold := by
  have h : threshold^2-(vertex threshold-1)^2=0 := by
    rw [threshold_vertex]
    ring
  apply Complex.ext
  · change sgn*Real.sqrt (threshold^2-(vertex threshold-1)^2)=0
    rw [h,Real.sqrt_zero,mul_zero]
  · exact threshold_vertex

end Manuscript15.DiskFamily20261127
#print axioms Manuscript15.DiskFamily20261127.first_min_radius_eq
#print axioms Manuscript15.DiskFamily20261127.second_min_radius_eq
#print axioms Manuscript15.DiskFamily20261127.first_extremizer_iff
#print axioms Manuscript15.DiskFamily20261127.second_extremizer_iff
#print axioms Manuscript15.DiskFamily20261127.threshold_vertex
#print axioms Manuscript15.DiskFamily20261127.threshold_coalescence
