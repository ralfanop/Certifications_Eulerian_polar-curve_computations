import EulerianGrothendieck.ComplexArcsineDisk

/-! M15 Lemma 8.1 (27 November 2026): variable-radius disk.
The scalar minimisation is independent of the analytic branch. Reuse the
existing H0, sqrtOneSub, branch identities and sharp half-radius theorem.
No new axioms. The statements below are CI candidates until checked. -/
noncomputable section
open Complex Filter Topology
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

/-- Extension of the existing branch derivative proof; the upper half-plane
case directly uses the original theorem. -/
theorem disk_hasDerivAt {z : ℂ} {r : ℝ} (hz : z ∈ disk r)
    (hr : r < Real.sqrt 2) : HasDerivAt H0 (1/sqrtOneSub z) z := by
  by_cases hpos : 0 < z.im
  · exact hasDerivAt_H0 hpos
  have hw := disk_slit hz hr
  have hw0 := Complex.slitPlane_ne_zero hw
  have hsq := sqrtOneSub_sq z
  have hs0 : sqrtOneSub z ≠ 0 := by
    intro h
    apply hw0
    rw [← hsq,h]
    norm_num
  have h1 : HasDerivAt (fun z : ℂ => 1-z^2) (-(2*z)) z := by
    simpa using ((hasDerivAt_pow 2 z).const_sub 1)
  have h2 : HasDerivAt sqrtOneSub ((1/2 : ℂ) * (1-z^2)^((1/2 : ℂ)-1) * (-(2*z))) z :=
    h1.cpow_const hw
  have hpow : (1-z^2)^((1/2 : ℂ)-1) = sqrtOneSub z/(1-z^2) := by
    rw [Complex.cpow_sub _ _ hw0,Complex.cpow_one]; rfl
  rw [hpow] at h2
  have h3 : HasDerivAt (fun z : ℂ => I*z+sqrtOneSub z)
      (I+(1/2 : ℂ)*(sqrtOneSub z/(1-z^2))*(-(2*z))) z := by
    simpa using (((hasDerivAt_id z).const_mul I).add h2)
  have h4 := (h3.clog (branch_mem_slitPlane z)).const_mul (-I)
  have hb := branch_ne_zero z
  have hderiv : -I*((I+(1/2 : ℂ)*(sqrtOneSub z/(1-z^2))*(-(2*z)))/
      (I*z+sqrtOneSub z)) = 1/sqrtOneSub z := by
    rw [← hsq]
    have e1 : (1/2 : ℂ)*(sqrtOneSub z/sqrtOneSub z^2)*(-(2*z)) = -(z/sqrtOneSub z) := by
      field_simp <;> ring
    have e2 : I + -(z/sqrtOneSub z) = (I*sqrtOneSub z-z)/sqrtOneSub z := by
      field_simp <;> ring
    have e3 : -I*(I*sqrtOneSub z-z) = I*z+sqrtOneSub z := by
      linear_combination (-(sqrtOneSub z))*I_sq
    rw [e1,e2,div_div,← mul_div_assoc,e3,mul_comm (sqrtOneSub z) (I*z+sqrtOneSub z),
      ← div_div,div_self hb]
  exact h4.congr_deriv hderiv

theorem norm_branch_derivative (z : ℂ) :
    ‖1/sqrtOneSub z‖ = 1/Real.sqrt ‖1-z^2‖ := by
  rw [norm_div,norm_one,← norm_sqrtOneSub_sq,Real.sqrt_sq (norm_nonneg _)]

/-- Mean-value upper estimate from a positive squared modulus bound. -/
theorem lipschitz_from_modulus {r m : ℝ} (hr : r < Real.sqrt 2) (hm : 0 < m)
    (hmin : ∀ z ∈ disk r, m ≤ ‖1-z^2‖^2) {z w : ℂ}
    (hz : z ∈ disk r) (hw : w ∈ disk r) :
    ‖H0 z-H0 w‖ ≤ (1/Real.sqrt (Real.sqrt m))*‖z-w‖ := by
  have hc : Convex ℝ (disk r) := convex_closedBall _ _
  apply hc.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := H0) (f' := fun x => 1/sqrtOneSub x)
    (fun x hx => (disk_hasDerivAt hx hr).hasDerivWithinAt) _ hw hz
  intro x hx
  have h1 := Real.sqrt_le_sqrt (hmin x hx)
  rw [Real.sqrt_sq (norm_nonneg _)] at h1
  have h2 := Real.sqrt_le_sqrt h1
  have hp : 0 < Real.sqrt (Real.sqrt m) := Real.sqrt_pos.2 (Real.sqrt_pos.2 hm)
  have hxpos : 0 < Real.sqrt ‖1-x^2‖ := lt_of_lt_of_le hp h2
  rw [norm_branch_derivative]
  exact (div_le_div_iff₀ hxpos hp).2 (by linarith)

/-- A Lipschitz constant bounds the norm of the derivative at any
boundary point: take a one-sided radial difference quotient into the disk. -/
theorem boundary_derivative_le_lipschitz {r L : ℝ} {z : ℂ}
    (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (hz : ‖z-I‖ = r)
    (hL : ∀ a ∈ disk r, ∀ b ∈ disk r, ‖H0 a-H0 b‖ ≤ L*‖a-b‖) :
    ‖1/sqrtOneSub z‖ ≤ L := by
  have hzmem : z ∈ disk r := by
    simpa [disk,Metric.mem_closedBall,Complex.dist_eq,hz]
  let d : ℂ := I-z
  have hdn : ‖d‖ = r := by
    dsimp [d]
    rw [show I-z = -(z-I) by ring,norm_neg,hz]
  have hg : HasDerivAt (fun h : ℝ => z+d*(h:ℂ)) d 0 := by
    simpa using (((hasDerivAt_id (0:ℝ)).ofReal_comp).const_mul d).const_add z
  have hd' : HasDerivAt H0 (1/sqrtOneSub z) (z+d*((0:ℝ):ℂ)) := by
    simpa using disk_hasDerivAt hzmem hr2
  have hcomp : HasDerivAt (fun h : ℝ => H0 (z+d*(h:ℂ)))
      (1/sqrtOneSub z*d) 0 :=
    HasDerivAt.comp (h₂ := H0) (h := fun h : ℝ => z+d*(h:ℂ)) (0:ℝ) hd' hg
  have hnorm := (continuous_norm.tendsto _).comp hcomp.tendsto_slope_zero_right
  have key : ‖1/sqrtOneSub z*d‖ ≤ L*r := by
    apply le_of_tendsto hnorm
    have hmem : ∀ᶠ h in 𝓝[>] (0:ℝ), h < 1 := by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with h hh using hh.2
    filter_upwards [self_mem_nhdsWithin,hmem] with h hp h1
    have hp' : 0 < h := hp
    simp only [Function.comp,Complex.ofReal_zero,mul_zero,add_zero,zero_add]
    have he : z+d*(h:ℂ)-I = ((1-h:ℝ):ℂ)*(z-I) := by
      dsimp [d]
      push_cast
      ring
    have hw : z+d*(h:ℂ) ∈ disk r := by
      rw [disk,Metric.mem_closedBall,Complex.dist_eq,he,norm_mul,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos (sub_pos.mpr h1),hz]
      nlinarith
    have hb := hL _ hw z hzmem
    rw [show z+d*(h:ℂ)-z = d*(h:ℂ) by ring,norm_mul,hdn,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hp'] at hb
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hp',inv_mul_le_iff₀ hp']
    calc
      ‖H0 (z+d*(h:ℂ))-H0 z‖ ≤ L*(r*h) := hb
      _ = h*(L*r) := by ring
  rw [norm_mul,hdn] at key
  exact le_of_mul_le_mul_right key hr

theorem boundary_norm_eq_radius {z : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : z.re^2+(z.im-1)^2=r^2) : ‖z-I‖=r := by
  rw [boundary_coords] at h
  nlinarith [norm_nonneg (z-I)]

/-- The least Lipschitz constant is the inverse fourth root of the attained
positive minimum of the squared modulus. No maximum-modulus assumption. -/
theorem sharp_from_boundary_min {r m : ℝ} {z : ℂ}
    (hr : 0 < r) (hr2 : r < Real.sqrt 2) (hm : 0 < m)
    (hz : ‖z-I‖=r) (he : ‖1-z^2‖^2=m)
    (hmin : ∀ w ∈ disk r, m ≤ ‖1-w^2‖^2) :
    IsLeast {L : ℝ | ∀ a ∈ disk r, ∀ b ∈ disk r, ‖H0 a-H0 b‖ ≤ L*‖a-b‖}
      (1/Real.sqrt (Real.sqrt m)) := by
  refine ⟨fun a ha b hb => lipschitz_from_modulus hr2 hm hmin ha hb,?_⟩
  intro L hL
  have h := boundary_derivative_le_lipschitz hr hr2 hz hL
  rw [norm_branch_derivative] at h
  have he' : Real.sqrt m = ‖1-z^2‖ := by
    rw [← he,Real.sqrt_sq (norm_nonneg _)]
  rwa [he']

theorem first_regime_sharp {r : ℝ} (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (hl : r ≤ threshold) :
    IsLeast {L : ℝ | ∀ a ∈ disk r, ∀ b ∈ disk r, ‖H0 a-H0 b‖ ≤ L*‖a-b‖}
      (1/Real.sqrt (1+(1-r)^2)) := by
  have hm : 0 < (1+(1-r)^2)^2 := by positivity
  have hh := sharp_from_boundary_min hr hr2 hm
    (boundary_norm_eq_radius hr.le (first_point_radius r))
    (first_point_value r) (fun w hw => disk_first_lower hw hr2 hl)
  simpa only [Real.sqrt_sq (show 0 ≤ 1+(1-r)^2 by positivity)] using hh

theorem second_regime_sharp {r : ℝ} (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (hl : threshold ≤ r) :
    IsLeast {L : ℝ | ∀ a ∈ disk r, ∀ b ∈ disk r, ‖H0 a-H0 b‖ ≤ L*‖a-b‖}
      (1/Real.sqrt (Real.sqrt ((2-r^2)^2/2))) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := mul_pos (sub_pos.mpr hr2) (show 0 < Real.sqrt 2+r by positivity)
  have h0 : 0 < 2-r^2 := by nlinarith
  have hm : 0 < (2-r^2)^2/2 := by positivity
  have hsgn : (1:ℝ)^2=1 := by norm_num
  exact sharp_from_boundary_min hr hr2 hm
    (boundary_norm_eq_radius hr.le (second_point_radius hr hr2 hl hsgn))
    (second_point_value hr hr2 hl hsgn) (fun w hw => disk_second_lower hw hr2)

theorem second_regime_formula {r : ℝ} (hr : 0 < r) (hr2 : r < Real.sqrt 2) :
    1/Real.sqrt (Real.sqrt ((2-r^2)^2/2)) =
      Real.sqrt (Real.sqrt 2)/Real.sqrt (2-r^2) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := mul_pos (sub_pos.mpr hr2) (show 0 < Real.sqrt 2+r by positivity)
  have h0 : 0 < 2-r^2 := by nlinarith
  rw [Real.sqrt_div' _ (by norm_num),Real.sqrt_sq h0.le,
    Real.sqrt_div' _ (Real.sqrt_nonneg 2)]
  have h1 : 0 < Real.sqrt (2-r^2) := Real.sqrt_pos.2 h0
  have h2 : 0 < Real.sqrt (Real.sqrt 2) := by positivity
  field_simp

theorem second_regime_sharp_explicit {r : ℝ} (hr : 0 < r) (hr2 : r < Real.sqrt 2)
    (hl : threshold ≤ r) :
    IsLeast {L : ℝ | ∀ a ∈ disk r, ∀ b ∈ disk r, ‖H0 a-H0 b‖ ≤ L*‖a-b‖}
      (Real.sqrt (Real.sqrt 2)/Real.sqrt (2-r^2)) := by
  rw [← second_regime_formula hr hr2]
  exact second_regime_sharp hr hr2 hl

/-- Metallic ratio with a real, nonnegative parameter. -/
def metallic (n : ℝ) : ℝ := (n+Real.sqrt (n^2+4))/2

theorem metallic_pos {n : ℝ} (hn : 0 ≤ n) : 0 < metallic n := by
  unfold metallic
  positivity

theorem metallic_quadratic (n : ℝ) : metallic n^2-n*metallic n-1=0 := by
  unfold metallic
  have hs := Real.sq_sqrt (show 0 ≤ n^2+4 by positivity)
  nlinarith

theorem metallic_difference {n : ℝ} (hn : 0 ≤ n) :
    metallic n-1/metallic n=n := by
  have hp := metallic_pos hn
  have hq := metallic_quadratic n
  have h : 1/metallic n = metallic n-n := by
    apply (div_eq_iff hp.ne').2
    nlinarith
  rw [h]
  ring


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

#print axioms Manuscript15.DiskFamily20261127.disk_hasDerivAt
#print axioms Manuscript15.DiskFamily20261127.norm_branch_derivative
#print axioms Manuscript15.DiskFamily20261127.lipschitz_from_modulus

#print axioms Manuscript15.DiskFamily20261127.boundary_derivative_le_lipschitz
#print axioms Manuscript15.DiskFamily20261127.boundary_norm_eq_radius
#print axioms Manuscript15.DiskFamily20261127.sharp_from_boundary_min
#print axioms Manuscript15.DiskFamily20261127.first_regime_sharp
#print axioms Manuscript15.DiskFamily20261127.second_regime_sharp

#print axioms Manuscript15.DiskFamily20261127.second_regime_formula
#print axioms Manuscript15.DiskFamily20261127.second_regime_sharp_explicit
#print axioms Manuscript15.DiskFamily20261127.metallic_pos
#print axioms Manuscript15.DiskFamily20261127.metallic_quadratic
#print axioms Manuscript15.DiskFamily20261127.metallic_difference
