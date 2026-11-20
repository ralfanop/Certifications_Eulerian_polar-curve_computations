import UniformLanczos.Profile
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Research extension of Manuscript 12: strict Jensen concavity of its actual
limit profile. No approximation to the inverse cumulant or the integral is used.
The pointwise second-derivative claim is a separate, stronger follow-up. -/

open Real Set Filter Topology

namespace UniformLanczos.ProfileConcavity

open UniformLanczos UniformLanczos.Profile

private noncomputable def g (x : ℝ) : ℝ :=
  x * (3 + 2 * sinh x ^ 2) - 3 * sinh x * cosh x

private theorem g_pos {x : ℝ} (hx : 0 < x) : 0 < g x := by
  have hd (s : ℝ) : HasDerivAt g (4 * sinh s * (s * cosh s - sinh s)) s := by
    have h₁ := ((hasDerivAt_id s).mul
      (((hasDerivAt_sinh s).pow 2).const_mul 2 |>.const_add 3))
    have h₂ := ((hasDerivAt_sinh s).mul (hasDerivAt_cosh s)).const_mul 3
    convert h₁.sub h₂ using 1
    · rfl
    · simp only [id, one_mul]
      rw [cosh_sq]
      ring
  have hm : StrictMonoOn g (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact (fun s _ => (hd s).continuousAt.continuousWithinAt)
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact mul_pos (mul_pos (by norm_num) (sinh_pos_iff.mpr hs))
        (sub_pos.mpr (sinh_lt_mul_cosh hs))
  have h := hm (show (0:ℝ) ∈ Ici 0 from le_rfl) hx.le hx
  simpa [g] using h

private noncomputable def q (x : ℝ) : ℝ :=
  if x = 0 then 1 else sinh x / x

private theorem q_continuous : Continuous q := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have h := (hasDerivAt_sinh 0).continuousAt_div
    convert h using 1
    funext y
    by_cases hy : y = 0 <;> simp [q, Function.update, hy]
  · have he : (fun y : ℝ => sinh y / y) =ᶠ[𝓝 x] q := by
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      simp [q, hy]
    exact ((continuous_sinh.continuousAt.div continuousAt_id hx).congr he)

private noncomputable def r (x : ℝ) : ℝ := q x ^ 3 / cosh x

private theorem r_eq {x : ℝ} (hx : x ≠ 0) :
    r x = sinh x ^ 3 / (x ^ 3 * cosh x) := by
  simp [r, q, hx, div_pow, div_div_eq_mul_div, div_div]

/-- Hyperbolic inequality used in the sign of the derivative of the variance. -/
theorem sinh_cube_gt {x : ℝ} (hx : 0 < x) :
    x ^ 3 * cosh x < sinh x ^ 3 := by
  have hm : StrictMonoOn r (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact ((q_continuous.pow 3).div continuous_cosh
        (fun y => (cosh_pos y).ne')).continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      have hden : s ^ 3 * cosh s ≠ 0 := by positivity
      have h₁ := (hasDerivAt_sinh s).pow 3
      have h₂ := (hasDerivAt_pow 3 s).mul (hasDerivAt_cosh s)
      have he : (fun y : ℝ => sinh y ^ 3 / (y ^ 3 * cosh y)) =ᶠ[𝓝 s] r := by
        filter_upwards [isOpen_ne.mem_nhds hs.ne'] with y hy
        exact (r_eq hy).symm
      have hd := (h₁.div h₂ hden).congr_of_eventuallyEq he.symm
      rw [hd.deriv]
      have hcalc :
          (3 * sinh s ^ (3 - 1) * cosh s * (s ^ 3 * cosh s) -
            sinh s ^ 3 * (3 * s ^ (3 - 1) * cosh s + s ^ 3 * sinh s)) /
            (s ^ 3 * cosh s) ^ 2 =
          sinh s ^ 2 * g s / (s ^ 4 * cosh s ^ 2) := by
        norm_num [g]
        field_simp [hs.ne', (cosh_pos s).ne']
        rw [cosh_sq]
        ring
      have hp : 0 < sinh s ^ 2 * g s / (s ^ 4 * cosh s ^ 2) :=
        div_pos (mul_pos (pow_pos (sinh_pos_iff.mpr hs) _) (g_pos hs)) (by positivity)
      first
      | simpa only [hcalc] using hp
      | convert hp using 1 <;> norm_num <;>
          field_simp [hs.ne', (cosh_pos s).ne'] <;> simp [g, cosh_sq] <;> ring
  have h := hm (show (0:ℝ) ∈ Ici 0 from le_rfl) hx.le hx
  have hr0 : r 0 = 1 := by simp [r, q]
  rw [hr0, r_eq hx.ne'] at h
  have hd : 0 < x ^ 3 * cosh x := by positivity
  simpa using (lt_div_iff₀ hd).mp h

/-- The variance Lpp decreases strictly on the positive axis. -/
theorem Lpp_strictAntiOn : StrictAntiOn Lpp (Ioi 0) := by
  have hd (s : ℝ) (hs : 0 < s) :
      HasDerivAt Lpp (cosh (s / 2) / (4 * sinh (s / 2) ^ 3) - 2 / s ^ 3) s := by
    have hsh : 0 < sinh (s / 2) := sinh_pos_iff.mpr (by positivity)
    have he : (fun y : ℝ => 1 / y ^ 2 - 1 / (4 * sinh (y / 2) ^ 2)) =ᶠ[𝓝 s] Lpp := by
      filter_upwards [isOpen_ne.mem_nhds hs.ne'] with y hy
      simp [Lpp, exp_div_sq_eq hy]
    refine HasDerivAt.congr_of_eventuallyEq ?_ he.symm
    have h₁ := (hasDerivAt_const s (1:ℝ)).div (hasDerivAt_pow 2 s) (by positivity)
    have h₂ := (hasDerivAt_sinh (s / 2)).comp s ((hasDerivAt_id s).div_const 2)
    have h₃ := (hasDerivAt_const s (1:ℝ)).div ((h₂.pow 2).const_mul 4) (by positivity)
    convert h₁.sub h₃ using 1
    · rfl
    · simp only [id, one_mul, zero_mul, zero_sub, Function.comp_apply]
      norm_num
      field_simp [hs.ne', hsh.ne']
      ring
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioi] at hs
    rw [(hd s hs).deriv]
    have hh := sinh_cube_gt (show 0 < s / 2 by positivity)
    have hsh : 0 < sinh (s / 2) := sinh_pos_iff.mpr (by positivity)
    apply sub_neg.mpr
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith

theorem Lp_strictConcave : StrictConcaveOn ℝ (Ici 0) Lp := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ici 0) Lp_continuous.continuousOn
  rw [interior_Ici]
  intro x hx y hy hxy
  rw [(hasDerivAt_Lp (show x ≠ 0 from (show 0 < x from hx).ne')).deriv,
      (hasDerivAt_Lp (show y ≠ 0 from (show 0 < y from hy).ne')).deriv]
  exact Lpp_strictAntiOn hx hy hxy

theorem Ip_strictConvex : StrictConvexOn ℝ (Ico 0 (1 / 2)) Ip := by
  refine ⟨convex_Ico 0 (1 / 2), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hxI := mem_Ioo_of hx.1 hx.2
  have hyI := mem_Ioo_of hy.1 hy.2
  have hi : Ip x ≠ Ip y := fun h => hxy (by simpa only [Lp_Ip hxI, Lp_Ip hyI] using congrArg Lp h)
  have hc := Lp_strictConcave.2 (show Ip x ∈ Ici 0 from Ip_nonneg hx.1 hx.2)
    (show Ip y ∈ Ici 0 from Ip_nonneg hy.1 hy.2) hi ha hb hab
  simp only [smul_eq_mul, Lp_Ip hxI, Lp_Ip hyI] at hc
  have hz := (convex_Ico (0:ℝ) (1/2)) hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hz ⊢
  apply Lp_strictMono.lt_iff_lt.mp
  rw [Lp_Ip (mem_Ioo_of hz.1 hz.2)]
  exact hc

theorem hasDerivAt_Ip_pos {y : ℝ} (hy : 0 < y) (hy' : y < 1/2) :
    HasDerivAt Ip (Lpp (Ip y))⁻¹ y := by
  have hyI := mem_Ioo_of hy.le hy'
  have hs : 0 < Ip y := by
    have h := Ip_strictMonoOn (mem_Ioo_of le_rfl (by norm_num)) hyI hy
    simpa using h
  apply HasDerivAt.of_local_left_inverse
    (Ip_continuousOn.continuousAt (Ioo_mem_nhds hyI.1 hyI.2))
    (hasDerivAt_Lp hs.ne') (Lpp_pos hs).ne'
  filter_upwards [Ioo_mem_nhds hyI.1 hyI.2] with z hz
  exact Lp_Ip hz

private theorem Ip_ratio_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) (hy : y < 1/2) :
    Ip x / x < Ip y / y := by
  have hy0 : 0 < y := hx.trans hxy
  have ha : 0 < 1 - x/y := by rw [sub_pos, div_lt_one hy0]; exact hxy
  have hb : 0 < x/y := div_pos hx hy0
  have hc := Ip_strictConvex.2 (show (0:ℝ) ∈ Ico 0 (1/2) from ⟨le_rfl, by norm_num⟩)
    (show y ∈ Ico 0 (1/2) from ⟨hy0.le, hy⟩) hy0.ne' ha hb (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Ip_zero] at hc
  rw [div_mul_cancel₀ _ hy0.ne'] at hc
  rw [div_lt_div_iff₀ hx hy0]
  have h := (lt_div_iff₀ hy0).mp (show Ip x < x * Ip y / y by
    calc Ip x < x / y * Ip y := hc
         _ = x * Ip y / y := by ring)
  exact h

noncomputable def K (z : ℝ) : ℝ := sqrt z * Ip (sqrt z)
noncomputable def J (z : ℝ) : ℝ := H (sqrt z)

private theorem sqrt_mem {z : ℝ} (hz : z ∈ Ioo 0 (1/4)) :
    sqrt z ∈ Ioo 0 (1/2) := by
  have h := Real.sq_sqrt hz.1.le
  have h0 := Real.sqrt_nonneg z
  exact ⟨Real.sqrt_pos.2 hz.1, by nlinarith [hz.2]⟩

private theorem K_hasDeriv {z : ℝ} (hz : z ∈ Ioo 0 (1/4)) :
    HasDerivAt K ((Ip (sqrt z) / sqrt z + (Lpp (Ip (sqrt z)))⁻¹) / 2) z := by
  have hs := sqrt_mem hz
  have hd := Real.hasDerivAt_sqrt hz.1.ne'
  have hi := (hasDerivAt_Ip_pos hs.1 hs.2).comp z hd
  convert hd.mul hi using 1
  · rfl
  · field_simp [hs.1.ne']
    ring

theorem K_strictConvex : StrictConvexOn ℝ (Ioo 0 (1/4)) K := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ioo 0 (1/4))
  · exact fun z hz => (K_hasDeriv hz).continuousAt.continuousWithinAt
  · rw [isOpen_Ioo.interior_eq]
    intro x hx y hy hxy
    rw [(K_hasDeriv hx).deriv, (K_hasDeriv hy).deriv]
    have sx := sqrt_mem hx
    have sy := sqrt_mem hy
    have hxy' : sqrt x < sqrt y := by
      have h1 := Real.sq_sqrt hx.1.le
      have h2 := Real.sq_sqrt hy.1.le
      by_contra! hn
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (add_nonneg sx.1.le sy.1.le)]
    have hi := Ip_strictMonoOn (mem_Ioo_of sx.1.le sx.2)
      (mem_Ioo_of sy.1.le sy.2) hxy'
    have hposx : 0 < Ip (sqrt x) := by
      have := Ip_strictMonoOn (mem_Ioo_of le_rfl (by norm_num)) (mem_Ioo_of sx.1.le sx.2) sx.1
      simpa using this
    have hposy : 0 < Ip (sqrt y) := hposx.trans hi
    have hvar := Lpp_strictAntiOn hposx hposy hi
    have hrec := one_div_lt_one_div_of_lt (Lpp_pos hposy) hvar
    have hratio := Ip_ratio_lt sx.1 hxy' sy.2
    simp only [one_div] at hrec
    linarith

private theorem integrand_eq {z θ : ℝ} (hz : 0 ≤ z) (hθ : 0 ≤ sin θ) :
    K (z * sin θ ^ 2) = (sqrt z * sin θ) * Ip (sqrt z * sin θ) := by
  simp [K, Real.sqrt_mul hz, Real.sqrt_sq_eq_abs, abs_of_nonneg hθ]

private theorem integrand_cont {z : ℝ} (hz : z ∈ Ioo 0 (1/4)) :
    ContinuousOn (fun θ => sqrt z * sin θ * Ip (sqrt z * sin θ)) (Icc 0 (π/2)) := by
  have hs := sqrt_mem hz
  exact (Ip_G_continuousOn hs.2).comp (continuous_const.mul continuous_sin).continuousOn
    (fun θ hθ => mul_sin_mem ⟨hs.1.le, le_rfl⟩ hθ)

theorem J_strictConvex : StrictConvexOn ℝ (Ioo 0 (1/4)) J := by
  refine ⟨convex_Ioo 0 (1/4), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hz := (convex_Ioo (0:ℝ) (1/4)) hx hy ha.le hb.le hab
  simp only [smul_eq_mul] at hz ⊢
  let z := a*x+b*y
  have hz' : z ∈ Ioo 0 (1/4) := hz
  let f (w θ : ℝ) := sqrt w * sin θ * Ip (sqrt w * sin θ)
  have hcx : ContinuousOn (f x) (Icc 0 (π/2)) := integrand_cont hx
  have hcy : ContinuousOn (f y) (Icc 0 (π/2)) := integrand_cont hy
  have hcz : ContinuousOn (f z) (Icc 0 (π/2)) := integrand_cont hz'
  have hcr : ContinuousOn (fun θ => a*f x θ+b*f y θ) (Icc 0 (π/2)) :=
    (continuousOn_const.mul hcx).add (continuousOn_const.mul hcy)
  have hpoint (θ : ℝ) (hθ : θ ∈ Ioc 0 (π/2)) : f z θ < a*f x θ+b*f y θ := by
    have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, pi_pos])
    have hs1 : sin θ ≤ 1 := sin_le_one _
    have hc : 0 < sin θ ^ 2 := by positivity
    have hc1 : sin θ ^ 2 ≤ 1 := by nlinarith
    have hm (w : ℝ) (hw : w ∈ Ioo 0 (1/4)) : w * sin θ ^ 2 ∈ Ioo 0 (1/4) :=
      ⟨mul_pos hw.1 hc, (mul_le_of_le_one_right hw.1.le hc1).trans_lt hw.2⟩
    have hn : x * sin θ ^ 2 ≠ y * sin θ ^ 2 := fun he => hxy ((mul_right_cancel₀ hc.ne') he)
    have hp := K_strictConvex.2 (hm x hx) (hm y hy) hn ha hb hab
    simp only [smul_eq_mul] at hp
    have he : a * (x*sin θ^2) + b * (y*sin θ^2) = z * sin θ ^ 2 := by dsimp [z]; ring
    rw [he, integrand_eq hz'.1.le hs.le, integrand_eq hx.1.le hs.le,
      integrand_eq hy.1.le hs.le] at hp
    exact hp
  have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (show (0:ℝ) < π/2 by positivity) hcz hcr
    (fun θ hθ => (hpoint θ hθ).le)
    ⟨π/2, ⟨by positivity, le_rfl⟩, hpoint _ ⟨by positivity, le_rfl⟩⟩
  have hxi : IntervalIntegrable (f x) MeasureTheory.volume 0 (π/2) := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le (by positivity)]
  have hyi : IntervalIntegrable (f y) MeasureTheory.volume 0 (π/2) := by
    apply ContinuousOn.intervalIntegrable
    rwa [uIcc_of_le (by positivity)]
  rw [intervalIntegral.integral_add (hxi.const_mul a) (hyi.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hlt
  have hscaled := mul_lt_mul_of_pos_left hlt (show (0:ℝ) < 1/π by positivity)
  unfold J H Hint
  change (1/π) * (∫ θ in (0:ℝ)..π/2, f z θ) <
    a * ((1/π) * ∫ θ in (0:ℝ)..π/2, f x θ) +
    b * ((1/π) * ∫ θ in (0:ℝ)..π/2, f y θ)
  linarith

private theorem J_strictMono : StrictMonoOn J (Ioo 0 (1/4)) := by
  intro x hx y hy hxy
  have sx := sqrt_mem hx
  have sy := sqrt_mem hy
  apply H_strictMonoOn (Ioo_subset_Ico_self sx) (Ioo_subset_Ico_self sy)
  have h1 := Real.sq_sqrt hx.1.le
  have h2 := Real.sq_sqrt hy.1.le
  by_contra! hn
  nlinarith [mul_nonneg (sub_nonneg.mpr hn) (add_nonneg sx.1.le sy.1.le)]

private theorem sq_ξ_mem {t : ℝ} (ht : 0 < t) : ξ t ^ 2 ∈ Ioo 0 (1/4) := by
  have h := (ξ_spec ht).1
  exact ⟨by positivity, by nlinarith [h.1, h.2]⟩

private theorem J_sq_ξ {t : ℝ} (ht : 0 < t) : J (ξ t ^ 2) = t := by
  unfold J
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (ξ_spec ht).1.1, (ξ_spec ht).2]

/-- The actual Manuscript 12 limiting profile is strictly concave on (0,∞)
in the Jensen sense. Unlike a local expansion, this covers arbitrary positive inputs. -/
theorem F_strictConcaveOn : StrictConcaveOn ℝ (Ioi 0) F := by
  refine ⟨convex_Ioi 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : 0 < x := hx
  have hy' : 0 < y := hy
  have hxm := sq_ξ_mem hx'
  have hym := sq_ξ_mem hy'
  have hne : ξ x ^ 2 ≠ ξ y ^ 2 := by
    intro he
    exact hxy (by simpa only [J_sq_ξ hx', J_sq_ξ hy'] using congrArg J he)
  have h := J_strictConvex.2 hxm hym hne ha hb hab
  simp only [smul_eq_mul, J_sq_ξ hx', J_sq_ξ hy'] at h
  have hw : 0 < a*x+b*y := by positivity
  have hm := (convex_Ioo (0:ℝ) (1/4)) hxm hym ha.le hb.le hab
  simp only [smul_eq_mul] at hm
  have hlt : a*ξ x^2+b*ξ y^2 < ξ (a*x+b*y)^2 := by
    by_contra! hn
    have hh := J_strictMono.monotoneOn (sq_ξ_mem hw) hm hn
    rw [J_sq_ξ hw] at hh
    linarith
  simp only [smul_eq_mul, F]
  linarith

#print axioms sinh_cube_gt
#print axioms Lpp_strictAntiOn
#print axioms Ip_strictConvex
#print axioms K_strictConvex
#print axioms J_strictConvex
#print axioms F_strictConcaveOn

end UniformLanczos.ProfileConcavity
