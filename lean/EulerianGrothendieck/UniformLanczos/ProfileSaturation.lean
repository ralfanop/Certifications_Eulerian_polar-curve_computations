import UniformLanczos.Profile
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Quantitative saturation of the M12 Lanczos profile
Research extension to Corollary 5.10, not a claim about the frozen manuscript.
The existing inverse bounds reduce the integral to a rational trigonometric
pole model with bounded error. Evaluate that model by an arctan primitive,
then transport the exact leading limit through the existing inverse profile.
-/

open Set Filter Topology Real intervalIntegral
open UniformLanczos

namespace UniformLanczos.Saturation
open Profile

noncomputable def pole (y : ℝ) : ℝ := y / (1 / 2 - y)

/-- The inverse bounds give a uniformly bounded integrand error. -/
theorem pole_pointwise {y : ℝ} (hy0 : 0 ≤ y) (hy : y < 1 / 2) :
    |y * Ip y - pole y| ≤ 1 := by
  have hlo := Ip_lower hy0 hy
  have hup : Ip y ≤ 1 / (1 / 2 - y) := by
    rcases eq_or_lt_of_le hy0 with h | h
    · subst y
      rw [Ip_zero]
      norm_num
    · exact (Profile.Ip_lt y h hy).le
  have h₁ := mul_le_mul_of_nonneg_left hlo hy0
  have h₂ := mul_le_mul_of_nonneg_left hup hy0
  rw [abs_le]
  unfold pole
  rw [div_eq_mul_one_div]
  constructor <;> nlinarith

/-- The error of the full pole model is at most 1/2 independently of a. -/
theorem pole_error {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1 / 2) :
    |H a - Hint pole a| ≤ 1 / 2 := by
  have hp : ContinuousOn pole (Icc 0 a) := by
    unfold pole
    exact continuousOn_id.div (continuousOn_const.sub continuousOn_id)
      (fun y hy => by linarith [hy.2])
  exact Hint_close ha (Ip_G_continuousOn ha') hp
    (fun y hy => pole_pointwise hy.1 (lt_of_le_of_lt hy.2 ha')) a ⟨ha, le_rfl⟩

noncomputable def angle (θ : ℝ) : ℝ := (θ - π / 2) / 2
noncomputable def q (a : ℝ) : ℝ := √(1 + 2*a) / √(1 - 2*a)
noncomputable def primitive (a θ : ℝ) : ℝ :=
  (2 / (√(1 - 2*a) * √(1 + 2*a))) * arctan (q a * tan (angle θ))

theorem pole_primitive {a θ : ℝ} (ha : 0 ≤ a) (ha' : a < 1 / 2)
    (hθ : θ ∈ Icc 0 (π/2)) :
    HasDerivAt (primitive a) (1/(1-2*a*sin θ)) θ := by
  have hd : 0 < 1 - 2*a := by linarith
  have he : 0 < 1 + 2*a := by linarith
  have hd0 := (Real.sqrt_pos.2 hd).ne'
  have he0 := (Real.sqrt_pos.2 he).ne'
  have hc : 0 < cos (angle θ) := by
    apply cos_pos_of_mem_Ioo
    unfold angle
    constructor <;> linarith [hθ.1, hθ.2, pi_pos]
  have hangle : HasDerivAt angle (1/2) θ := by
    unfold angle
    simpa using ((hasDerivAt_id θ).sub_const (π/2)).div_const 2
  have htan := (hasDerivAt_tan hc.ne').comp θ hangle
  have hg : HasDerivAt (fun z => q a * tan (angle z))
      (q a * (1 / cos (angle θ)^2 * (1/2))) θ := by
    simpa [Function.comp_def] using htan.const_mul (q a)
  have hder := hg.arctan.const_mul (2 / (√(1 - 2*a) * √(1 + 2*a)))
  have hsin : sin θ = cos (angle θ)^2 - sin (angle θ)^2 := by
    calc
      sin θ = cos (θ - π/2) := by rw [cos_sub, cos_pi_div_two, sin_pi_div_two]; ring
      _ = cos (2 * angle θ) := by congr 1; unfold angle; ring
      _ = _ := by
        rw [cos_two_mul]
        nlinarith [sin_sq_add_cos_sq (angle θ)]
  have hpos : 0 < 1-2*a*sin θ := by
    have hs := sin_le_one θ
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hs)]
  have hq : 0 < q a := by unfold q; positivity
  have hcros : √(1-2*a) * √(1+2*a) = (1-2*a) * q a := by
    unfold q
    rw [← mul_div_assoc]
    apply (eq_div_iff hd0).2
    calc
      √(1-2*a)*√(1+2*a)*√(1-2*a) = (√(1-2*a))^2*√(1+2*a) := by ring
      _ = _ := by rw [sq_sqrt hd.le]
  have hq2 : (1-2*a)*(q a)^2 = 1+2*a := by
    unfold q
    rw [div_pow, sq_sqrt hd.le, sq_sqrt he.le]
    field_simp [hd.ne']
  have hsum : (1-2*a)*(cos (angle θ)^2+(q a)^2*sin (angle θ)^2) =
      1-2*a*sin θ := by
    rw [mul_add, ← mul_assoc, hq2, hsin]
    nlinarith [sin_sq_add_cos_sq (angle θ)]
  have hcalc : (2 / (√(1-2*a)*√(1+2*a))) *
      (1/(1+(q a*tan (angle θ))^2) *
      (q a * (1/cos (angle θ)^2*(1/2)))) = 1/(1-2*a*sin θ) := by
    rw [hcros, ← hsum, tan_eq_sin_div_cos]
    have hden : 1 + (q a * (sin (angle θ) / cos (angle θ)))^2 ≠ 0 := by positivity
    have hden' : (1-2*a)*(cos (angle θ)^2+(q a)^2*sin (angle θ)^2) ≠ 0 := by
      rw [hsum]; exact hpos.ne'
    field_simp [hd.ne', hq.ne', hc.ne', hden, hden']
    <;> ring
  simpa only [primitive, hcalc] using hder

/-- Exact finite-interval pole integral, with all denominators positive. -/
theorem pole_integral {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) :
    (∫ θ in (0:ℝ)..(π/2), 1/(1-2*a*sin θ)) =
      (2 / (√(1-2*a)*√(1+2*a))) * arctan (q a) := by
  have hπ : (0:ℝ) ≤ π/2 := by positivity
  have hi : IntervalIntegrable (fun θ : ℝ => 1/(1-2*a*sin θ))
      MeasureTheory.volume 0 (π/2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuous_sin.continuousOn))
    intro θ hθ
    have hs := sin_le_one θ
    have hh : 0 < 1-2*a*sin θ := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hs)]
    exact hh.ne'
  have hx := integral_eq_sub_of_hasDerivAt (f := primitive a)
    (fun θ hθ => pole_primitive ha ha' (by rwa [uIcc_of_le hπ] at hθ)) hi
  rw [hx]
  unfold primitive angle
  have h0 : ((0:ℝ)-π/2)/2 = -(π/4) := by ring
  rw [h0]
  simp [tan_neg, tan_pi_div_four, arctan_neg]

theorem pole_model_formula {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) :
    Hint pole a + 1/2 =
      (1/π) * ((2 / (√(1-2*a)*√(1+2*a))) * arctan (q a)) := by
  have hπ : (0:ℝ) ≤ π/2 := by positivity
  have hI : IntervalIntegrable (fun θ : ℝ => 1/(1-2*a*sin θ))
      MeasureTheory.volume 0 (π/2) := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (continuousOn_const.sub (continuousOn_const.mul continuous_sin.continuousOn))
    intro θ _
    have hs := sin_le_one θ
    have hh : 0 < 1-2*a*sin θ := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hs)]
    exact hh.ne'
  unfold Hint
  have hEq : (∫ θ in (0:ℝ)..(π/2), pole (a*sin θ)) =
      ∫ θ in (0:ℝ)..(π/2), (1/(1-2*a*sin θ)-1) := by
    apply integral_congr
    intro θ _
    unfold pole
    have hs := sin_le_one θ
    have hh : 0 < 1-2*a*sin θ := by nlinarith [mul_nonneg ha (sub_nonneg.mpr hs)]
    have hh' : 0 < 1/2-a*sin θ := by linarith
    rw [show 1-2*a*sin θ = 2*(1/2-a*sin θ) by ring]
    field_simp [hh'.ne']
    <;> ring
  rw [hEq, integral_sub hI intervalIntegral.intervalIntegrable_const, pole_integral ha ha', integral_const]
  simp only [sub_zero, smul_eq_mul, mul_one]
  field_simp [pi_ne_zero]
  <;> ring

noncomputable def normalModel (a : ℝ) : ℝ :=
  √2 / (π * √(1+2*a)) * arctan (q a)

theorem normalized_model {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) :
    √(1/2-a) * (Hint pole a + 1/2) = normalModel a := by
  rw [pole_model_formula ha ha']
  unfold normalModel
  have hd : 0 < 1/2-a := by linarith
  have he : 0 < 1+2*a := by linarith
  rw [show 1-2*a = 2*(1/2-a) by ring, Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ))]
  have htwo : (2:ℝ)/√2 = √2 := by
    apply (div_eq_iff (sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne').2
    nlinarith [sq_sqrt (by norm_num : (0:ℝ)≤2)]
  calc
    _ = (2/√2)/(π*√(1+2*a))*arctan (q a) := by
      field_simp [pi_ne_zero, (sqrt_pos.2 hd).ne', (sqrt_pos.2 he).ne',
        (sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'] <;> ring
      rw [mul_right_comm, mul_inv_cancel₀ (sqrt_pos.2 hd).ne', one_mul]
    _ = _ := by rw [htwo]

theorem q_profile_atTop : Tendsto (fun t : ℝ => q (ξ t)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  have hx := ξ_tendsto
  have hδ : Tendsto (fun t : ℝ => 1-2*ξ t) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hx) using 1 <;> norm_num
  have hB : Tendsto (fun t : ℝ => (max B 0)^2 * (1-2*ξ t)) atTop (𝓝 0) := by
    have hcB : Tendsto (fun _ : ℝ => (max B 0)^2) atTop (𝓝 ((max B 0)^2)) := tendsto_const_nhds
    simpa using hcB.mul hδ
  filter_upwards [eventually_gt_atTop (0:ℝ), hB.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1))] with t ht hb
  have ha := (ξ_spec ht).1
  have hd : 0 < 1-2*ξ t := by linarith [ha.2]
  have he : 0 < 1+2*ξ t := by linarith [ha.1]
  unfold q
  have hsq : (max B 0 * √(1-2*ξ t))^2 < (√(1+2*ξ t))^2 := by
    rw [mul_pow, sq_sqrt hd.le, sq_sqrt he.le]
    linarith [ha.1]
  have hnon : 0 ≤ max B 0 * √(1-2*ξ t) := by positivity
  have hlt : max B 0 * √(1-2*ξ t) < √(1+2*ξ t) := by
    by_contra! hn
    have hm := mul_nonneg (sub_nonneg.mpr hn) (add_nonneg hnon (sqrt_nonneg (1+2*ξ t)))
    nlinarith
  apply le_trans (le_max_left B 0)
  exact (le_div_iff₀ (sqrt_pos.2 hd)).2 hlt.le

theorem normalized_model_tendsto :
    Tendsto (fun t : ℝ => normalModel (ξ t)) atTop (𝓝 (1/2)) := by
  have he : Tendsto (fun t : ℝ => 1+2*ξ t) atTop (𝓝 2) := by
    convert tendsto_const_nhds.add (tendsto_const_nhds.mul ξ_tendsto) using 1 <;> norm_num
  have hs : Tendsto (fun t : ℝ => √(1+2*ξ t)) atTop (𝓝 (√2)) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp he
  have hπ : Tendsto (fun t : ℝ => π * √(1+2*ξ t)) atTop (𝓝 (π*√2)) :=
    tendsto_const_nhds.mul hs
  have hd : π * √(2:ℝ) ≠ 0 := by positivity
  have hf : Tendsto (fun t : ℝ => √2/(π*√(1+2*ξ t))) atTop (𝓝 (√2/(π*√2))) :=
    tendsto_const_nhds.div hπ hd
  have hA := (tendsto_arctan_atTop.comp q_profile_atTop).mono_right nhdsWithin_le_nhds
  convert hf.mul hA using 1
  <;> first | rfl | field_simp [pi_ne_zero, (sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne']

theorem root_rate : Tendsto (fun t : ℝ => t * √(1/2-ξ t)) atTop (𝓝 (1/2)) := by
  have hδ : Tendsto (fun t : ℝ => 1/2-ξ t) atTop (𝓝 0) := by
    convert tendsto_const_nhds.sub ξ_tendsto using 1 <;> norm_num
  have hs : Tendsto (fun t : ℝ => √(1/2-ξ t)) atTop (𝓝 0) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hδ
  have hD : Tendsto (fun t : ℝ => t * √(1/2-ξ t) - normalModel (ξ t)) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero, Real.norm_eq_abs]
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hs
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    obtain ⟨ha, hH⟩ := ξ_spec ht
    have hE := pole_error ha.1.le ha.2
    rw [hH] at hE
    rw [← normalized_model ha.1.le ha.2]
    have hs0 : 0 ≤ √(1/2-ξ t) := sqrt_nonneg _
    rw [show t * √(1/2-ξ t) - √(1/2-ξ t)*(Hint pole (ξ t)+1/2) =
      √(1/2-ξ t)*(t-Hint pole (ξ t)-1/2) by ring, abs_mul, abs_of_nonneg hs0]
    have he : |t-Hint pole (ξ t)-1/2| ≤ 1 := by
      rw [abs_le] at hE ⊢
      constructor <;> linarith
    simpa using mul_le_mul_of_nonneg_left he hs0
  convert hD.add normalized_model_tendsto using 1
  · funext t; ring
  · norm_num

/-- Saturation with the sharp coefficient 1/16. -/
theorem profile_saturation :
    Tendsto (fun t : ℝ => t^2 * (1/16-F t)) atTop (𝓝 (1/16)) := by
  have hfac : Tendsto (fun t : ℝ => (1/2+ξ t)/4) atTop (𝓝 (1/4)) := by
    convert (tendsto_const_nhds.add ξ_tendsto).div_const 4 using 1 <;> norm_num
  have h := (root_rate.pow 2).mul hfac
  have hh : Tendsto (fun t : ℝ => (t*√(1/2-ξ t))^2*((1/2+ξ t)/4))
      atTop (𝓝 (1/16)) := by convert h using 1 <;> norm_num
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have ha := (ξ_spec ht).1
  rw [mul_pow, sq_sqrt (by linarith [ha.2] : 0 ≤ 1/2-ξ t)]
  unfold F
  ring

end UniformLanczos.Saturation

#print axioms UniformLanczos.Saturation.pole_pointwise
#print axioms UniformLanczos.Saturation.pole_error
#print axioms UniformLanczos.Saturation.pole_primitive
#print axioms UniformLanczos.Saturation.pole_integral
#print axioms UniformLanczos.Saturation.pole_model_formula
#print axioms UniformLanczos.Saturation.normalized_model
#print axioms UniformLanczos.Saturation.q_profile_atTop
#print axioms UniformLanczos.Saturation.normalized_model_tendsto
#print axioms UniformLanczos.Saturation.root_rate
#print axioms UniformLanczos.Saturation.profile_saturation
