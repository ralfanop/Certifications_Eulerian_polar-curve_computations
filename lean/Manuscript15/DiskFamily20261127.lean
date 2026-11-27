import EulerianGrothendieck.ComplexArcsineDisk

/-! M15 Lemma 8.1 (27 November 2026): variable-radius disk.
The scalar minimisation is independent of the analytic branch. Reuse the
existing H0, sqrtOneSub, branch identities and sharp half-radius theorem.
No new axioms. The statements below are CI candidates until checked. -/
noncomputable section
open Complex
namespace Manuscript15.DiskFamily20261127
open EulerianGrothendieck.ArcsinDisk

def threshold : ℝ := 2 - Real.sqrt 2
def vertex (r : ℝ) : ℝ := (2-r^2)/4
def q (r y : ℝ) : ℝ := 8*y^2+4*(r^2-2)*y+(r^2-2)^2
def disk (r : ℝ) : Set ℂ := Metric.closedBall I r

theorem disk_half : disk (1/2) = diskB := rfl

theorem threshold_pos : 0 < threshold := by
  unfold threshold
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  nlinarith

theorem threshold_lt_one : threshold < 1 := by
  unfold threshold
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  nlinarith

theorem vertex_difference (r : ℝ) :
    vertex r - (1-r) = -(r^2-4*r+2)/4 := by
  unfold vertex
  ring

theorem threshold_sign {r : ℝ} (hr : r < Real.sqrt 2) :
    (0 ≤ r^2-4*r+2 ↔ r ≤ threshold) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp : 0 < 2-r+Real.sqrt 2 := by linarith
  have he : r^2-4*r+2 = (2-r-Real.sqrt 2)*(2-r+Real.sqrt 2) := by
    nlinarith
  rw [he, mul_nonneg_iff]
  unfold threshold
  constructor
  · rintro (⟨h,_⟩ | ⟨_,h⟩)
    · linarith
    · linarith
  · intro h
    exact Or.inl ⟨by linarith,hp.le⟩

theorem complete_square (r y : ℝ) :
    q r y = 8*(y-vertex r)^2+(2-r^2)^2/2 := by
  unfold q vertex
  ring

theorem lower_arc_difference (r y : ℝ) :
    q r y - (1+(1-r)^2)^2 =
      (y-(1-r))*(8*(y-(1-r))+4*(r^2-4*r+2)) := by
  unfold q
  ring

theorem boundary_polynomial (z : ℂ) (r : ℝ)
    (h : z.re^2+(z.im-1)^2 = r^2) :
    ‖1-z^2‖^2 = q r z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply, one_sub_sq_re, one_sub_sq_im]
  have hx : z.re^2 = r^2-(z.im-1)^2 := by linarith
  have hs : z.re^2+z.im^2+1 = r^2+2*z.im := by nlinarith
  calc
    _ = (z.re^2+z.im^2+1)^2-4*z.re^2 := by ring
    _ = q r z.im := by rw [hs,hx]; unfold q; ring

theorem first_boundary_min {r y : ℝ} (hr : r < Real.sqrt 2)
    (hsmall : r ≤ threshold) (hy : 1-r ≤ y) :
    (1+(1-r)^2)^2 ≤ q r y := by
  have hs := (threshold_sign hr).2 hsmall
  have hp := mul_nonneg (sub_nonneg.mpr hy)
    (show 0 ≤ 8*(y-(1-r))+4*(r^2-4*r+2) by linarith)
  linarith [lower_arc_difference r y]

theorem first_boundary_unique {r y : ℝ} (hr : r < Real.sqrt 2)
    (hsmall : r ≤ threshold) (hy : 1-r ≤ y)
    (he : q r y = (1+(1-r)^2)^2) : y = 1-r := by
  by_contra hn
  have hd : 0 < y-(1-r) := sub_pos.mpr (lt_of_le_of_ne hy (Ne.symm hn))
  have hs := (threshold_sign hr).2 hsmall
  have hp := mul_pos hd
    (show 0 < 8*(y-(1-r))+4*(r^2-4*r+2) by linarith)
  linarith [lower_arc_difference r y]

theorem second_boundary_min (r y : ℝ) :
    (2-r^2)^2/2 ≤ q r y := by
  linarith [complete_square r y, sq_nonneg (y-vertex r)]

theorem second_boundary_unique {r y : ℝ}
    (h : q r y = (2-r^2)^2/2) : y = vertex r := by
  have hs : (y-vertex r)^2 = 0 := by linarith [complete_square r y]
  nlinarith [sq_nonneg (y-vertex r)]

theorem vertex_feasible {r : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hlarge : threshold ≤ r) :
    1-r ≤ vertex r ∧ vertex r ≤ 1+r := by
  have hp : 0 < 2-r+Real.sqrt 2 := by linarith
  have hm : 2-r-Real.sqrt 2 ≤ 0 := by unfold threshold at hlarge; linarith
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hq : r^2-4*r+2 ≤ 0 := by
    have hh := mul_nonpos_of_nonpos_of_nonneg hm hp.le
    nlinarith
  constructor
  · linarith [vertex_difference r]
  · unfold vertex
    nlinarith [sq_nonneg r]

theorem boundary_coords (z : ℂ) :
    z.re^2+(z.im-1)^2 = ‖z-I‖^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, sub_zero]
  <;> ring

theorem disk_radius_bound {z : ℂ} {r : ℝ} (hz : z ∈ disk r) :
    ‖z-I‖ ≤ r := by
  simpa [disk, Metric.mem_closedBall, Complex.dist_eq] using hz

theorem disk_first_lower {z : ℂ} {r : ℝ} (hz : z ∈ disk r)
    (hr : r < Real.sqrt 2) (hsmall : r ≤ threshold) :
    (1+(1-r)^2)^2 ≤ ‖1-z^2‖^2 := by
  let s := ‖z-I‖
  have hs : 0 ≤ s := norm_nonneg _
  have hsr : s ≤ r := disk_radius_bound hz
  have hy : 1-s ≤ z.im := by
    have h := Complex.abs_im_le_norm (z-I)
    simp only [Complex.sub_im, Complex.I_im] at h
    have h' := (abs_le.mp h).1
    change -s ≤ z.im-1 at h'
    linarith
  have hmin := first_boundary_min (lt_of_le_of_lt hsr hr) (le_trans hsr hsmall) hy
  have hcoords : z.re^2+(z.im-1)^2 = s^2 := boundary_coords z
  have h0 : 0 ≤ 1-r := by linarith [threshold_lt_one]
  have h1 : 1-r ≤ 1-s := by linarith
  have h2 := pow_le_pow_left₀ h0 h1 2
  have h3 : 1+(1-r)^2 ≤ 1+(1-s)^2 := by linarith
  have h4 := pow_le_pow_left₀ (show 0 ≤ 1+(1-r)^2 by positivity) h3 2
  rw [boundary_polynomial z s hcoords]
  exact h4.trans hmin

theorem disk_second_lower {z : ℂ} {r : ℝ} (hz : z ∈ disk r)
    (hr : r < Real.sqrt 2) :
    (2-r^2)^2/2 ≤ ‖1-z^2‖^2 := by
  let s := ‖z-I‖
  have hs : 0 ≤ s := norm_nonneg _
  have hsr : s ≤ r := disk_radius_bound hz
  have hr0 : 0 ≤ r := hs.trans hsr
  have hs2 := pow_le_pow_left₀ hs hsr 2
  have hr2 := pow_le_pow_left₀ hr0 hr.le 2
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)] at hr2
  have h0 : 0 ≤ 2-r^2 := by linarith
  have h1 : 2-r^2 ≤ 2-s^2 := by linarith
  have h2 := pow_le_pow_left₀ h0 h1 2
  have hcoords : z.re^2+(z.im-1)^2 = s^2 := boundary_coords z
  rw [boundary_polynomial z s hcoords]
  exact (show (2-r^2)^2/2 ≤ (2-s^2)^2/2 by linarith).trans (second_boundary_min s z.im)

theorem half_radius_sharp :
    IsLeast {L : ℝ | ∀ z ∈ disk (1/2), ∀ w ∈ disk (1/2),
      ‖H0 z-H0 w‖ ≤ L*‖z-w‖} (2/Real.sqrt 5) := by
  rw [disk_half]
  exact H0_lipschitz_constant

/-- Cassini curvature contact: algebraic equivalence, not a Taylor theorem. -/
theorem curvature_contact {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    (1-t^2)/(t*(1+t^2)) = 1/(1-t) ↔ t^2+2*t-1 = 0 := by
  have h0 : t*(1+t^2) ≠ 0 := by positivity
  have h1 : 1-t ≠ 0 := by linarith
  rw [div_eq_div_iff h0 h1]
  constructor <;> intro h <;> nlinarith

def firstPoint (r : ℝ) : ℂ := ⟨0,1-r⟩
def secondPoint (r sgn : ℝ) : ℂ :=
  ⟨sgn * Real.sqrt (r^2-(vertex r-1)^2),vertex r⟩

theorem disk_mem_of_coords {z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : z.re^2+(z.im-1)^2 ≤ r^2) : z ∈ disk r := by
  rw [boundary_coords] at h
  have hle : ‖z-I‖ ≤ r := by
    by_contra! hh
    have hp := mul_pos (sub_pos.mpr hh) (show 0 < ‖z-I‖+r by linarith)
    nlinarith
  simpa [disk,Metric.mem_closedBall,Complex.dist_eq] using hle

theorem first_point_radius (r : ℝ) :
    (firstPoint r).re^2+((firstPoint r).im-1)^2 = r^2 := by
  change (0:ℝ)^2+(1-r-1)^2 = r^2
  ring

theorem first_point_value (r : ℝ) :
    ‖1-(firstPoint r)^2‖^2 = (1+(1-r)^2)^2 := by
  rw [boundary_polynomial _ _ (first_point_radius r)]
  change q r (1-r) = _
  unfold q
  ring

theorem second_point_radius {r sgn : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hl : threshold ≤ r)
    (hsgn : sgn^2=1) :
    (secondPoint r sgn).re^2+((secondPoint r sgn).im-1)^2 = r^2 := by
  obtain ⟨hlo,hhi⟩ := vertex_feasible hr hr2 hl
  have hp := mul_nonneg (show 0 ≤ r-(vertex r-1) by linarith)
    (show 0 ≤ r+(vertex r-1) by linarith)
  have hn : 0 ≤ r^2-(vertex r-1)^2 := by nlinarith
  change (sgn * Real.sqrt (r^2-(vertex r-1)^2))^2+(vertex r-1)^2 = r^2
  rw [mul_pow,hsgn,Real.sq_sqrt hn]
  ring

theorem second_point_value {r sgn : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hl : threshold ≤ r)
    (hsgn : sgn^2=1) :
    ‖1-(secondPoint r sgn)^2‖^2 = (2-r^2)^2/2 := by
  rw [boundary_polynomial _ _ (second_point_radius hr hr2 hl hsgn)]
  change q r (vertex r) = _
  rw [complete_square]
  ring

theorem second_points_distinct {r : ℝ} (hr : 0 < r)
    (hr2 : r < Real.sqrt 2) (hl : threshold < r) :
    secondPoint r 1 ≠ secondPoint r (-1) := by
  have hpoly : r^2-4*r+2 < 0 := lt_of_not_ge
    (fun h => (not_le_of_gt hl) ((threshold_sign hr2).1 h))
  have hlo' : 1-r < vertex r := by linarith [vertex_difference r]
  have hhi' : vertex r < 1+r := by unfold vertex; nlinarith [sq_nonneg r]
  have hp := mul_pos (show 0 < r-(vertex r-1) by linarith)
    (show 0 < r+(vertex r-1) by linarith)
  have hn : 0 < r^2-(vertex r-1)^2 := by nlinarith
  intro he
  have hh := congrArg Complex.re he
  change (1:ℝ)*Real.sqrt (r^2-(vertex r-1)^2) =
    (-1:ℝ)*Real.sqrt (r^2-(vertex r-1)^2) at hh
  linarith [Real.sqrt_pos.2 hn]

theorem disk_slit {z : ℂ} {r : ℝ} (hz : z ∈ disk r) (hr : r < Real.sqrt 2) :
    1-z^2 ∈ Complex.slitPlane := by
  have hb := disk_radius_bound hz
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hb
  have hsq := pow_le_pow_left₀ (norm_nonneg (z-I)) hb 2
  rw [← boundary_coords] at hsq
  have hp := mul_pos (sub_pos.mpr hr)
    (show 0 < Real.sqrt 2 + r by linarith [Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)])
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hrr : r^2 < 2 := by nlinarith
  rw [Complex.mem_slitPlane_iff,one_sub_sq_re,one_sub_sq_im]
  by_cases hx : z.re = 0
  · left; rw [hx]; positivity
  by_cases hy : z.im = 0
  · left
    rw [hy] at hsq ⊢
    nlinarith
  · right
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num) hx) hy)

theorem disk_first_min {r : ℝ} (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (hl : r ≤ threshold) :
    IsLeast ((fun z : ℂ => ‖1-z^2‖^2) '' disk r) ((1+(1-r)^2)^2) := by
  refine ⟨⟨firstPoint r,disk_mem_of_coords hr.le (first_point_radius r).le,first_point_value r⟩,?_⟩
  rintro v ⟨z,hz,rfl⟩
  exact disk_first_lower hz hr2 hl

theorem disk_second_min {r : ℝ} (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (hl : threshold ≤ r) :
    IsLeast ((fun z : ℂ => ‖1-z^2‖^2) '' disk r) ((2-r^2)^2/2) := by
  have hsgn : (1:ℝ)^2=1 := by norm_num
  refine ⟨⟨secondPoint r 1,disk_mem_of_coords hr.le (second_point_radius hr hr2 hl hsgn).le,
    second_point_value hr hr2 hl hsgn⟩,?_⟩
  rintro v ⟨z,hz,rfl⟩
  exact disk_second_lower hz hr2

end Manuscript15.DiskFamily20261127
#print axioms Manuscript15.DiskFamily20261127.disk_half
#print axioms Manuscript15.DiskFamily20261127.threshold_pos
#print axioms Manuscript15.DiskFamily20261127.threshold_lt_one
#print axioms Manuscript15.DiskFamily20261127.vertex_difference
#print axioms Manuscript15.DiskFamily20261127.threshold_sign
#print axioms Manuscript15.DiskFamily20261127.complete_square
#print axioms Manuscript15.DiskFamily20261127.lower_arc_difference
#print axioms Manuscript15.DiskFamily20261127.boundary_polynomial
#print axioms Manuscript15.DiskFamily20261127.first_boundary_min
#print axioms Manuscript15.DiskFamily20261127.first_boundary_unique
#print axioms Manuscript15.DiskFamily20261127.second_boundary_min
#print axioms Manuscript15.DiskFamily20261127.second_boundary_unique
#print axioms Manuscript15.DiskFamily20261127.vertex_feasible
#print axioms Manuscript15.DiskFamily20261127.boundary_coords
#print axioms Manuscript15.DiskFamily20261127.disk_radius_bound
#print axioms Manuscript15.DiskFamily20261127.disk_first_lower
#print axioms Manuscript15.DiskFamily20261127.disk_second_lower
#print axioms Manuscript15.DiskFamily20261127.half_radius_sharp
#print axioms Manuscript15.DiskFamily20261127.curvature_contact

#print axioms Manuscript15.DiskFamily20261127.disk_mem_of_coords
#print axioms Manuscript15.DiskFamily20261127.first_point_radius
#print axioms Manuscript15.DiskFamily20261127.first_point_value
#print axioms Manuscript15.DiskFamily20261127.second_point_radius
#print axioms Manuscript15.DiskFamily20261127.second_point_value
#print axioms Manuscript15.DiskFamily20261127.second_points_distinct
#print axioms Manuscript15.DiskFamily20261127.disk_slit
#print axioms Manuscript15.DiskFamily20261127.disk_first_min
#print axioms Manuscript15.DiskFamily20261127.disk_second_min
