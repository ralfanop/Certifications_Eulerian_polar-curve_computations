import Bridge.Malmsten
import Bridge.MellinExtras
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Section 7: the integration by parts in (168)

`∫_0^∞ (1 - sech t)/t² dt = ∫_0^∞ tanh t sech t / t dt`, both integrals converging absolutely;
the boundary terms of `F(t) = (1 - sech t)/t` vanish at `0⁺` and at `∞`.
-/

open Real MeasureTheory Set Filter Topology

namespace EulerianBridge.MalmstenIBP

open EulerianBridge.Mellin

/-- `t cosh t - sinh t ≥ 0` for `t ≥ 0`. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : sinh t ≤ t * cosh t := by
  let g : ℝ → ℝ := fun t => t * cosh t - sinh t
  have hg : ∀ x, HasDerivAt g (x * sinh x) x := by
    intro x
    have := ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x)
    convert this using 1; simp
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hg x).continuousAt.continuousWithinAt
    · exact fun x _ => (hg x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hg x).deriv]
      exact mul_nonneg (le_of_lt hx) (sinh_nonneg_iff.mpr (le_of_lt hx))
  have := hmono (left_mem_Ici) ht ht
  simp [g] at this
  linarith

/-- `cosh t - 1 ≤ (t²/2) cosh t` for `t ≥ 0`. -/
theorem cosh_sub_one_le {t : ℝ} (ht : 0 ≤ t) : cosh t - 1 ≤ t ^ 2 / 2 * cosh t := by
  let g : ℝ → ℝ := fun t => t ^ 2 / 2 * cosh t - cosh t + 1
  have hg : ∀ x, HasDerivAt g ((x * cosh x - sinh x) + x ^ 2 / 2 * sinh x) x := by
    intro x
    have h1 := ((hasDerivAt_pow 2 x).div_const 2).mul (hasDerivAt_cosh x)
    have := (h1.sub (hasDerivAt_cosh x)).add_const 1
    convert this using 1; simp; ring
  have hmono : MonotoneOn g (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hg x).continuousAt.continuousWithinAt
    · exact fun x _ => (hg x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      rw [(hg x).deriv]
      have h1 := sinh_le_mul_cosh (le_of_lt hx)
      have h2 : 0 ≤ sinh x := sinh_nonneg_iff.mpr (le_of_lt hx)
      have h3 : 0 ≤ x ^ 2 / 2 * sinh x := by positivity
      linarith
  have := hmono (left_mem_Ici) ht ht
  simp [g] at this
  linarith

/-- `0 ≤ (1 - sech t)/t² ≤ 1/2` for `t > 0`. -/
theorem B_le {t : ℝ} (ht : 0 < t) : 0 ≤ (1 - sech t) / t ^ 2 ∧ (1 - sech t) / t ^ 2 ≤ 1 / 2 := by
  have hc : 0 < cosh t := cosh_pos t
  have hc1 : 1 ≤ cosh t := one_le_cosh t
  have h := cosh_sub_one_le ht.le
  unfold sech
  constructor
  · apply div_nonneg _ (by positivity)
    rw [sub_nonneg, div_le_one hc]; exact hc1
  · rw [div_le_iff₀ (by positivity), one_sub_div hc.ne', div_le_iff₀ hc]
    nlinarith

theorem B_le_inv_sq {t : ℝ} (ht : 0 < t) : (1 - sech t) / t ^ 2 ≤ 1 / t ^ 2 := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  unfold sech
  have : 0 < 1 / cosh t := by positivity
  linarith

/-- `0 ≤ tanh t sech t / t ≤ sech t ≤ 2 e^{-t}` for `t > 0`. -/
theorem A_le {t : ℝ} (ht : 0 < t) : 0 ≤ tanh t * sech t / t ∧ tanh t * sech t / t ≤ 2 * exp (-t) := by
  have hc : 0 < cosh t := cosh_pos t
  have hs : 0 ≤ sinh t := sinh_nonneg_iff.mpr ht.le
  have h1 := sinh_le_mul_cosh ht.le
  have hq : sech t ≤ 2 * exp (-t) := by
    have := EulerianBridge.MellinExtras.qE_le_exp t
    rwa [(qE_eq_sech t).1, abs_of_pos ht] at this
  have hsech : 0 < sech t := by unfold sech; positivity
  rw [tanh_eq_sinh_div_cosh]
  constructor
  · positivity
  · calc sinh t / cosh t * sech t / t ≤ sech t := by
          rw [div_le_iff₀ ht, div_mul_eq_mul_div, div_le_iff₀ hc]
          nlinarith
      _ ≤ 2 * exp (-t) := hq

theorem measurable_sech : Measurable sech := by
  unfold sech; exact (continuous_const.div continuous_cosh (fun x => (cosh_pos x).ne')).measurable

theorem integrableOn_B : IntegrableOn (fun t => (1 - sech t) / t ^ 2) (Ioi 0) := by
  have hmeas : Measurable (fun t : ℝ => (1 - sech t) / t ^ 2) :=
    (measurable_const.sub measurable_sech).div (measurable_id.pow_const 2)
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · refine Measure.integrableOn_of_bounded (M := 1 / 2) (by simp) hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall (fun t ht => ?_))
    obtain ⟨h0, h1⟩ := B_le ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  · have hi : IntegrableOn (fun t : ℝ => t ^ (-2:ℝ)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine hi.mono' hmeas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    obtain ⟨h0, -⟩ := B_le ht0
    rw [Real.norm_eq_abs, abs_of_nonneg h0, rpow_neg ht0.le, rpow_two, ← one_div]
    exact B_le_inv_sq ht0

theorem integrableOn_A : IntegrableOn (fun t => tanh t * sech t / t) (Ioi 0) := by
  have htanh : Measurable tanh := by
    have : tanh = fun x => sinh x / cosh x := funext tanh_eq_sinh_div_cosh
    rw [this]; exact (continuous_sinh.div continuous_cosh (fun x => (cosh_pos x).ne')).measurable
  have hmeas : Measurable (fun t : ℝ => tanh t * sech t / t) :=
    (htanh.mul measurable_sech).div measurable_id
  have hi : IntegrableOn (fun t : ℝ => 2 * exp (-t)) (Ioi 0) := by
    have := (integrableOn_exp_neg_Ioi 0)
    exact this.const_mul 2
  refine hi.mono' hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => ?_))
  obtain ⟨h0, h1⟩ := A_le ht
  rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1

/-- `F(t) = (1 - sech t)/t`, `F(0) = 0`. -/
noncomputable def F (t : ℝ) : ℝ := if t = 0 then 0 else (1 - sech t) / t

theorem hasDerivAt_sech (t : ℝ) : HasDerivAt sech (-(sinh t / cosh t ^ 2)) t := by
  unfold sech
  have := (hasDerivAt_cosh t).inv (cosh_pos t).ne'
  convert this using 1
  · funext x; simp
  · ring

theorem hasDerivAt_F {t : ℝ} (ht : 0 < t) :
    HasDerivAt F (tanh t * sech t / t - (1 - sech t) / t ^ 2) t := by
  have hev : (fun x => (1 - sech x) / x) =ᶠ[𝓝 t] F := by
    filter_upwards [lt_mem_nhds ht] with x hx
    unfold F; rw [if_neg hx.ne']
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have h := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_sech t)).div (hasDerivAt_id t) ht.ne'
  convert h using 1
  rw [tanh_eq_sinh_div_cosh]
  have hc : 0 < cosh t := cosh_pos t
  simp only [Pi.sub_apply, id, sech]
  field_simp
  ring

theorem F_tendsto_zero : Tendsto F (𝓝[>] 0) (𝓝 0) := by
  have hub : ∀ t ∈ Ioi (0:ℝ), F t ≤ t / 2 := by
    intro t ht
    have := (B_le ht).2
    unfold F; rw [if_neg (ne_of_gt ht)]
    rw [div_le_iff₀ (pow_pos ht 2)] at this
    rw [div_le_iff₀ ht]; nlinarith
  have hlb : ∀ t ∈ Ioi (0:ℝ), 0 ≤ F t := by
    intro t ht
    have := (B_le ht).1
    unfold F; rw [if_neg (ne_of_gt ht)]
    have h2 : (1 - sech t) / t = (1 - sech t) / t ^ 2 * t := by field_simp
    rw [h2]; exact mul_nonneg this (le_of_lt ht)
  have hlim : Tendsto (fun t : ℝ => t / 2) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => t / 2) (𝓝 0) (𝓝 (0 / 2)) := (continuous_id.div_const 2).tendsto 0
    rw [zero_div] at this; exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (eventually_nhdsWithin_of_forall hlb) (eventually_nhdsWithin_of_forall hub)

theorem F_continuousWithinAt : ContinuousWithinAt F (Ici 0) 0 := by
  rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
  have h0 : F 0 = 0 := by simp [F]
  rw [h0]; exact F_tendsto_zero

theorem F_tendsto_atTop : Tendsto F atTop (𝓝 0) := by
  have hub : ∀ᶠ t in atTop, F t ≤ 1 / t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    unfold F; rw [if_neg (ne_of_gt ht)]
    apply div_le_div_of_nonneg_right _ ht.le
    have : 0 < sech t := by unfold sech; positivity
    linarith
  have hlb : ∀ᶠ t in atTop, 0 ≤ F t := by
    filter_upwards [eventually_gt_atTop 0] with t ht
    have := (B_le ht).1
    unfold F; rw [if_neg (ne_of_gt ht)]
    have h2 : (1 - sech t) / t = (1 - sech t) / t ^ 2 * t := by field_simp
    rw [h2]; exact mul_nonneg this (le_of_lt ht)
  have hlim : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim hlb hub

/-- Eq. (168), first equality. -/
theorem catalan_ibp :
    ∫ t in Ioi (0:ℝ), (1 - sech t) / t ^ 2 = ∫ t in Ioi (0:ℝ), tanh t * sech t / t := by
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto F_continuousWithinAt
    (fun t ht => hasDerivAt_F ht) (integrableOn_A.sub integrableOn_B) F_tendsto_atTop
  rw [integral_sub integrableOn_A integrableOn_B] at hF
  have h0 : F 0 = 0 := by simp [F]
  rw [h0, sub_zero] at hF
  linarith

/-- Eq. (168) with the cited value (Abdulsalam): both integrals equal `(4/π) β(2)`, and (169). -/
theorem catalan_both (hA : ∫ t in Ioi (0:ℝ), (1 - sech t) / t ^ 2 = 4 / π * dirichletBeta 2) :
    ∫ t in Ioi (0:ℝ), tanh t * sech t / t = 4 / π * dirichletBeta 2 ∧
      ∫ t in Ioi (0:ℝ), (1 - qE t) / t ^ 2 = 2 * dirichletBeta 2 * EulerianBridge.Malmsten.rEpi :=
  ⟨by rw [← catalan_ibp, hA], EulerianBridge.Malmsten.catalan_q hA⟩

end EulerianBridge.MalmstenIBP
