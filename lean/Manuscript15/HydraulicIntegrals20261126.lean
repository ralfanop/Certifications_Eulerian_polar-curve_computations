import Mathlib

/-! M15 §§11–12, EQ499_508_SEPARATE. Actual sinc profile, interval
integrals and analytic bounds, plus integrability of the orbit
density at general parameter. The geometric isoperimetric and
cross-manuscript vacuum-limit identifications remain separate. -/

open Real MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace Manuscript15.HydraulicIntegrals20261126

def radial (t : ℝ) : ℝ := Real.sinc (t/2)
def slope (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..1, -(u/2)*Real.sin ((u/2)*t)

theorem radial_cosine_integral (t : ℝ) :
    radial t = ∫ u in (0:ℝ)..1, Real.cos ((t/2)*u) := by
  by_cases ht : t = 0
  · subst t
    simp [radial]
  · have ht2 : t/2 ≠ 0 := div_ne_zero ht two_ne_zero
    unfold radial
    rw [Real.sinc_of_ne_zero ht2]
    have h := intervalIntegral.mul_integral_comp_mul_left
      (f := Real.cos) (a := (0:ℝ)) (b := (1:ℝ)) (t/2)
    rw [mul_zero, mul_one, integral_cos, Real.sin_zero, sub_zero] at h
    apply (div_eq_iff ht2).2
    simpa only [mul_comm] using h.symm

theorem radial_hasDerivAt (t : ℝ) : HasDerivAt radial (slope t) t := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 1)
  let F (x u : ℝ) := Real.cos ((u/2)*x)
  let F' (x u : ℝ) := -(u/2)*Real.sin ((u/2)*x)
  have hi (x : ℝ) : Integrable (F x) μ :=
    ((by unfold F; fun_prop : Continuous (F x)).intervalIntegrable 0 1).1
  have hm : ∀ᶠ x in 𝓝 t, AEStronglyMeasurable (F x) μ :=
    Filter.Eventually.of_forall (fun x => (hi x).aestronglyMeasurable)
  have h'm : AEStronglyMeasurable (F' t) μ :=
    (by unfold F'; fun_prop : Continuous (F' t)).aestronglyMeasurable
  have hb : Integrable (fun u : ℝ => u/2) μ :=
    ((by fun_prop : Continuous (fun u : ℝ => u/2)).intervalIntegrable 0 1).1
  have hbound : ∀ᵐ u ∂μ, ∀ x ∈ (Set.univ : Set ℝ), ‖F' x u‖ ≤ u/2 := by
    dsimp [μ]
    filter_upwards [ae_restrict_mem (μ := volume) (s := Ioc (0:ℝ) 1) measurableSet_Ioc] with u hu
    intro x _
    have hu0 : 0 ≤ u/2 := by linarith [hu.1]
    change |-(u/2)*Real.sin ((u/2)*x)| ≤ u/2
    rw [abs_mul, abs_neg, abs_of_nonneg hu0]
    calc
      _ ≤ (u/2)*1 := mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hu0
      _ = _ := by ring
  have hd : ∀ᵐ u ∂μ, ∀ x ∈ (Set.univ : Set ℝ), HasDerivAt (fun y => F y u) (F' x u) x := by
    filter_upwards [] with u
    intro x _
    unfold F F'
    convert ((hasDerivAt_id x).const_mul (u/2)).cos using 1 <;>
      first | rfl | (simp only [id_eq]; ring) | ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := F') (bound := fun u => u/2)
    (s := Set.univ) (by simp : Set.univ ∈ 𝓝 t) hm (hi t) h'm hbound hb hd).2
  have hF : (fun x => ∫ u, F x u ∂μ) = radial := by
    funext x
    unfold μ F
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), radial_cosine_integral]
    apply intervalIntegral.integral_congr
    intro u _
    congr 1
    ring
  have hS : (∫ u, F' t u ∂μ) = slope t := by
    unfold μ F' slope
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [hF,hS] at h
  exact h

theorem slope_abs_bound (t : ℝ) : |slope t| ≤ 1/4 := by
  unfold slope
  have hc : Continuous (fun u : ℝ => |-(u/2)*Real.sin ((u/2)*t)|) := by fun_prop
  have hlin : Continuous (fun u : ℝ => u/2) := by fun_prop
  have hpoint : ∀ u ∈ Icc (0:ℝ) 1, |-(u/2)*Real.sin ((u/2)*t)| ≤ u/2 := by
    intro u hu
    have hu0 : 0 ≤ u/2 := by linarith [hu.1]
    rw [abs_mul, abs_neg, abs_of_nonneg hu0]
    calc
      _ ≤ (u/2)*1 := mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) hu0
      _ = _ := by ring
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (hc.intervalIntegrable 0 1) (hlin.intervalIntegrable 0 1) hpoint
  have hp : (∫ u in (0:ℝ)..1, u/2) = 1/4 := by
    have he : (∫ u in (0:ℝ)..1, u/2) = (1:ℝ)^2/4-(0:ℝ)^2/4 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun u : ℝ => u^2/4) (f' := fun u : ℝ => u/2)
      · intro u _
        convert ((hasDerivAt_id u).pow 2).div_const 4 using 1 <;>
          first | rfl | (simp only [id_eq]; ring) | ring
      · exact hlin.intervalIntegrable 0 1
    rw [he]
    norm_num
  exact (intervalIntegral.abs_integral_le_integral_abs (by norm_num)).trans (hm.trans_eq hp)

theorem radial_lower (t : ℝ) (ht : |t| ≤ Real.pi) : 2/Real.pi ≤ radial t := by
  have he : radial t = radial |t| := by
    unfold radial
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_div, Real.sinc_neg]
  rw [he]
  by_cases hz : |t| = 0
  · rw [hz]
    simp [radial]
    exact (div_le_iff₀ Real.pi_pos).2 (by linarith [Real.pi_gt_three])
  · have hp : 0 < |t|/2 := by positivity
    have hle : |t|/2 ≤ Real.pi/2 := by linarith
    unfold radial
    rw [Real.sinc_of_ne_zero hp.ne']
    exact (le_div_iff₀ hp).2 (Real.mul_le_sin hp.le hle)

theorem radial_derivative_bound (t : ℝ) : |deriv radial t| ≤ 1/4 := by
  rw [(radial_hasDerivAt t).deriv]
  exact slope_abs_bound t

theorem slope_lipschitz_bound (x y : ℝ) : |slope x-slope y| ≤ |x-y|/4 := by
  unfold slope
  let f (t u : ℝ) := -(u/2)*Real.sin ((u/2)*t)
  have hc (t : ℝ) : Continuous (f t) := by unfold f; fun_prop
  change |(∫ u in (0:ℝ)..1, f x u)-(∫ u in (0:ℝ)..1, f y u)| ≤ _
  rw [← intervalIntegral.integral_sub (hc x |>.intervalIntegrable 0 1)
    (hc y |>.intervalIntegrable 0 1)]
  have habs : Continuous (fun u => |f x u-f y u|) := (hc x |>.sub (hc y)).abs
  have hpoint : ∀ u ∈ Icc (0:ℝ) 1, |f x u-f y u| ≤ |x-y|/4 := by
    intro u hu
    have hu0 : 0 ≤ u/2 := by linarith [hu.1]
    have hu1 : u/2 ≤ 1/2 := by linarith [hu.2]
    have hEq : f x u-f y u = -(u/2)*(Real.sin ((u/2)*x)-Real.sin ((u/2)*y)) := by
      unfold f
      ring
    rw [hEq, abs_mul, abs_neg, abs_of_nonneg hu0]
    calc
      _ ≤ (u/2)*|((u/2)*x)-((u/2)*y)| :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le _ _) hu0
      _ = (u/2)^2*|x-y| := by
        rw [show (u/2)*x-(u/2)*y=(u/2)*(x-y) by ring,abs_mul,abs_of_nonneg hu0]
        ring
      _ ≤ |x-y|/4 := by
        have hs : (u/2)^2 ≤ 1/4 := by nlinarith [mul_nonneg (sub_nonneg.mpr hu1) hu0]
        calc
          _ ≤ (1/4)*|x-y| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
          _ = _ := by ring
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (habs.intervalIntegrable 0 1)
    (continuous_const.intervalIntegrable 0 1) hpoint
  have ha := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun u => f x u-f y u) (by norm_num : (0:ℝ) ≤ 1)
  exact ha.trans (by simpa using hm)

theorem slope_continuous : Continuous slope := by
  apply Metric.continuous_iff.2
  intro x ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  rw [Real.dist_eq] at hy ⊢
  have h := slope_lipschitz_bound y x
  linarith

-- Cauchy--Schwarz on a real interval, here proved by integrated variance.
theorem interval_square_integral_bound (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) (hab : a < b) :
    (∫ t in a..b, f t)^2 ≤ (b-a)*(∫ t in a..b, (f t)^2) := by
  let m := (∫ t in a..b, f t)/(b-a)
  have hm : m*(b-a) = ∫ t in a..b, f t := by
    dsimp [m]
    field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
  have hi : IntervalIntegrable (fun t => (f t)^2) volume a b :=
    (hf.pow 2).intervalIntegrable a b
  have hj : IntervalIntegrable (fun t => (2*m)*f t) volume a b :=
    (continuous_const.mul hf).intervalIntegrable a b
  have hk : IntervalIntegrable (fun _ : ℝ => m^2) volume a b :=
    continuous_const.intervalIntegrable a b
  have hnon : 0 ≤ ∫ t in a..b, (f t-m)^2 :=
    intervalIntegral.integral_nonneg_of_forall hab.le (fun _ => sq_nonneg _)
  have hEq : (∫ t in a..b, (f t-m)^2) =
      (∫ t in a..b, (f t)^2)-2*m*(∫ t in a..b, f t)+(b-a)*m^2 := by
    calc
      _ = ∫ t in a..b, (f t)^2-(2*m)*f t+m^2 := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (hi.sub hj) hk,
          intervalIntegral.integral_sub hi hj, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const, smul_eq_mul]
  rw [hEq, ← hm] at hnon
  have hmul := mul_nonneg (sub_nonneg.mpr hab.le) hnon
  rw [← hm]
  nlinarith

def polarArea : ℝ := ∫ t in (0:ℝ)..Real.pi, (radial t)^2
def polarPerimeter : ℝ :=
  2*(∫ t in (0:ℝ)..Real.pi, Real.sqrt ((radial t)^2+(slope t)^2))

theorem radial_continuous : Continuous radial :=
  Real.continuous_sinc.comp (continuous_id.div_const 2)

theorem radial_slope_energy_bound :
    (∫ t in (0:ℝ)..Real.pi, (slope t)^2) ≤
    (Real.pi^2/64)*polarArea := by
  have hf : Continuous (fun t : ℝ => (slope t)^2) := slope_continuous.pow 2
  have hg : Continuous (fun t => (Real.pi^2/64)*(radial t)^2) :=
    continuous_const.mul (radial_continuous.pow 2)
  have hp : ∀ t ∈ Icc (0:ℝ) Real.pi,
      (slope t)^2 ≤ (Real.pi^2/64)*(radial t)^2 := by
    intro t ht
    have hr := radial_lower t (by simpa [abs_of_nonneg ht.1] using ht.2)
    have hs := abs_le.mp (slope_abs_bound t)
    have h1 : (slope t)^2 ≤ 1/16 := by nlinarith
    have h2 : 0 < 2/Real.pi := by positivity
    have h3 : (2/Real.pi)^2 ≤ (radial t)^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ radial t+2/Real.pi by linarith)]
    have h4 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ Real.pi^2/64 by positivity)
    have h5 : (Real.pi^2/64)*(2/Real.pi)^2 = (1:ℝ)/16 := by
      field_simp [Real.pi_ne_zero] <;> ring
    rw [h5] at h4
    exact h1.trans h4
  have h := intervalIntegral.integral_mono_on (μ := volume) Real.pi_pos.le
    (hf.intervalIntegrable 0 Real.pi) (hg.intervalIntegrable 0 Real.pi) hp
  rw [intervalIntegral.integral_const_mul] at h
  exact h

theorem polar_area_positive : 0 < polarArea := by
  have hc : Continuous (fun t : ℝ => (radial t)^2) := radial_continuous.pow 2
  have h : (∫ t in (0:ℝ)..Real.pi, (2/Real.pi)^2) ≤ polarArea := by
    apply intervalIntegral.integral_mono_on Real.pi_pos.le
      (continuous_const.intervalIntegrable 0 Real.pi) (hc.intervalIntegrable 0 Real.pi)
    intro t ht
    have hr := radial_lower t (by simpa [abs_of_nonneg ht.1] using ht.2)
    have hp : 0 < 2/Real.pi := by positivity
    change (2/Real.pi)^2 ≤ (radial t)^2
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) (show 0 ≤ radial t+2/Real.pi by linarith)]
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  exact lt_of_lt_of_le (by positivity) h

theorem polar_perimeter_energy_bound :
    polarPerimeter^2 ≤ 4*Real.pi*(polarArea+∫ t in (0:ℝ)..Real.pi, (slope t)^2) := by
  let f (t : ℝ) := Real.sqrt ((radial t)^2+(slope t)^2)
  have hf : Continuous f := Real.continuous_sqrt.comp
    ((radial_continuous.pow 2).add (slope_continuous.pow 2))
  have h := interval_square_integral_bound f hf 0 Real.pi Real.pi_pos
  have he : (fun t => (f t)^2) = (fun t => (radial t)^2+(slope t)^2) := by
    funext t
    exact Real.sq_sqrt (by positivity)
  have hrad : IntervalIntegrable (fun t : ℝ => (radial t)^2) volume 0 Real.pi :=
    (radial_continuous.pow 2).intervalIntegrable 0 Real.pi
  have hslope : IntervalIntegrable (fun t : ℝ => (slope t)^2) volume 0 Real.pi :=
    (slope_continuous.pow 2).intervalIntegrable 0 Real.pi
  rw [he, intervalIntegral.integral_add hrad hslope, sub_zero] at h
  unfold polarPerimeter polarArea
  change (2*(∫ t in (0:ℝ)..Real.pi, f t))^2 ≤ _
  nlinarith

theorem polar_deficit_bound :
    (polarPerimeter/(2*Real.sqrt (Real.pi*polarArea)))^2 ≤ 1+Real.pi^2/64 := by
  have ha := polar_area_positive
  have hd : 0 < Real.pi*polarArea := mul_pos Real.pi_pos ha
  have hsq : (2*Real.sqrt (Real.pi*polarArea))^2 = 4*Real.pi*polarArea := by
    rw [mul_pow, Real.sq_sqrt hd.le]
    ring
  rw [div_pow, hsq]
  apply (div_le_iff₀ (by positivity : 0 < 4*Real.pi*polarArea)).2
  have h := polar_perimeter_energy_bound
  have h' := radial_slope_energy_bound
  have hm := mul_le_mul_of_nonneg_left h' (by positivity : 0 ≤ 4*Real.pi)
  nlinarith

-- §12: general positive orbit density, with genuine integrability.
def orbitDensity (b c x : ℝ) : ℝ := b / Real.sqrt ((1+x^2)*(x^2+c^2))

theorem orbit_density_continuous (b c : ℝ) (hc : 0 < c) :
    Continuous (orbitDensity b c) := by
  unfold orbitDensity
  apply continuous_const.div₀ (by fun_prop)
  intro x
  exact (Real.sqrt_pos.2 (by positivity)).ne'

theorem orbit_density_domination (b c x : ℝ) (hb : 0 < b)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖orbitDensity b c x‖ ≤ (b/c)*(1+x^2)⁻¹ := by
  have hA : 0 < 1+x^2 := by positivity
  have hC : 0 < Real.sqrt ((1+x^2)*(x^2+c^2)) := by
    exact Real.sqrt_pos.2 (by positivity)
  have hcs : c^2 ≤ 1 := by nlinarith
  have hcomp : c^2*(1+x^2) ≤ x^2+c^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcs) (sq_nonneg x)]
  have hs : (c*(1+x^2))^2 ≤ (1+x^2)*(x^2+c^2) := by
    nlinarith [mul_le_mul_of_nonneg_left hcomp hA.le]
  have hs2 : (Real.sqrt ((1+x^2)*(x^2+c^2)))^2 =
    (1+x^2)*(x^2+c^2) := Real.sq_sqrt (by positivity)
  have hle : c*(1+x^2) ≤ Real.sqrt ((1+x^2)*(x^2+c^2)) := by
    nlinarith
  unfold orbitDensity
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hb.le hC.le)]
  calc
    b/Real.sqrt ((1+x^2)*(x^2+c^2)) ≤ b/(c*(1+x^2)) :=
      div_le_div_of_nonneg_left hb.le (mul_pos hc hA) hle
    _ = _ := by field_simp [hc.ne',hA.ne'] <;> ring

theorem orbit_density_integrable (b c : ℝ) (hb : 0 < b)
    (hc : 0 < c) (hc1 : c ≤ 1) : Integrable (orbitDensity b c) := by
  have h := integrable_inv_one_add_sq.const_mul (b/c)
  refine Integrable.mono' h (orbit_density_continuous b c hc).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun x => orbit_density_domination b c x hb hc hc1)

end Manuscript15.HydraulicIntegrals20261126

#print axioms Manuscript15.HydraulicIntegrals20261126.radial_cosine_integral
#print axioms Manuscript15.HydraulicIntegrals20261126.radial_hasDerivAt
#print axioms Manuscript15.HydraulicIntegrals20261126.slope_abs_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.radial_lower
#print axioms Manuscript15.HydraulicIntegrals20261126.radial_derivative_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.slope_lipschitz_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.slope_continuous
#print axioms Manuscript15.HydraulicIntegrals20261126.interval_square_integral_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.radial_continuous
#print axioms Manuscript15.HydraulicIntegrals20261126.radial_slope_energy_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.polar_area_positive
#print axioms Manuscript15.HydraulicIntegrals20261126.polar_perimeter_energy_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.polar_deficit_bound
#print axioms Manuscript15.HydraulicIntegrals20261126.orbit_density_continuous
#print axioms Manuscript15.HydraulicIntegrals20261126.orbit_density_domination
#print axioms Manuscript15.HydraulicIntegrals20261126.orbit_density_integrable
