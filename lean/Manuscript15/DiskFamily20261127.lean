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
