import Manuscript15.CrossQuarticFinitePeriod20261125
import Mathlib

/-!
# M15 November 25: full analytic improper quartic-period identity

Source: Manuscript_15_20261125_CROSS_CONNECTIONS(1).zip,
Proposition 10.2, Eq. (555), label eq:cross-curvePeriod15.

This continues the EXACT-HEAD kernel-verified finite-interval identity
from PR #613. Here the analytical obligations are explicit:
- the true target elliptic integrand is integrable on (0,+∞);
- the true rational substitution z(r)=sqrt(2)*r/(1-r²)
  tends to +∞ as r approaches 1 from below;
- the source elliptic interval primitive is continuous at r=1;
- the finite-interval identity is passed to the limit
  using Mathlib's actual improper-integral convergence theorem.

This does not assert that the rational map extends to a degree-two
morphism between projective genus-one curves, nor the separate
self-dual crease Taylor remainder or its scaling limit.
-/

namespace Manuscript15.CrossQuarticImproperPeriod20261125

open MeasureTheory Set Filter
open Manuscript15.CrossQuartic20261125
open Manuscript15.CrossQuarticFinitePeriod20261125
open scoped Interval Topology

/-- The actual source elliptic integrand is continuous everywhere
on the real line, including the endpoint 1. -/
theorem sourceIntegrand_continuous : Continuous sourceIntegrand := by
  unfold sourceIntegrand
  have hden : Continuous (fun t : ℝ => Real.sqrt (1 + t ^ 4)) := by
    fun_prop
  have hne : ∀ t : ℝ, Real.sqrt (1 + t ^ 4) ≠ 0 := by
    intro t
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  exact continuous_const.div₀ hden hne

/-- The actual target elliptic integrand is continuous everywhere
on the real line, including z=0. -/
theorem targetIntegrand_continuous : Continuous targetIntegrand := by
  unfold targetIntegrand
  have hden : Continuous
      (fun z : ℝ => Real.sqrt ((1 + z ^ 2) * (1 + 2 * z ^ 2))) := by
    fun_prop
  have hne : ∀ z : ℝ,
      Real.sqrt ((1 + z ^ 2) * (1 + 2 * z ^ 2)) ≠ 0 := by
    intro z
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  exact continuous_const.div₀ hden hne

/-- The true target density is pointwise dominated by the
integrable Cauchy density 1/(1+z²). This supplies the required
absolute convergence at +∞. -/
theorem targetIntegrand_norm_bound (z : ℝ) :
    ‖targetIntegrand z‖ ≤ ‖(1 + z ^ 2)⁻¹‖ := by
  have hz : 0 ≤ z ^ 2 := sq_nonneg z
  have hA : 0 < 1 + z ^ 2 := by positivity
  have hB : 0 < 1 + 2 * z ^ 2 := by positivity
  have hprod : 0 ≤ (1 + z ^ 2) * (1 + 2 * z ^ 2) := by positivity
  have hrootPos :
      0 < Real.sqrt ((1 + z ^ 2) * (1 + 2 * z ^ 2)) := by
    exact Real.sqrt_pos.2 (mul_pos hA hB)
  have hrootSq :
      (Real.sqrt ((1 + z ^ 2) * (1 + 2 * z ^ 2))) ^ 2 =
        (1 + z ^ 2) * (1 + 2 * z ^ 2) :=
    Real.sq_sqrt hprod
  have hcompSq :
      (1 + z ^ 2) ^ 2 ≤
        (1 + z ^ 2) * (1 + 2 * z ^ 2) := by
    nlinarith [sq_nonneg z, sq_nonneg (z ^ 2)]
  have hrootLe :
      1 + z ^ 2 ≤ Real.sqrt ((1 + z ^ 2) * (1 + 2 * z ^ 2)) := by
    nlinarith
  have hupper : targetIntegrand z ≤ (1 + z ^ 2)⁻¹ := by
    unfold targetIntegrand
    simpa only [one_div] using one_div_le_one_div_of_le hA hrootLe
  have htargetNonneg : 0 ≤ targetIntegrand z := by
    unfold targetIntegrand
    positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg htargetNonneg,
    abs_of_nonneg (inv_nonneg.mpr hA.le), one_div] using hupper

/-- Absolute Lebesgue integrability of the target elliptic
period integrand on ALL of ℝ, and hence on (0,+∞). -/
theorem targetIntegrand_integrable : Integrable targetIntegrand := by
  refine Integrable.mono' integrable_inv_one_add_sq
    targetIntegrand_continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun z : ℝ => by
    have hh := targetIntegrand_norm_bound z
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 1 + z ^ 2))] using hh)

/-- The TRUE rational coordinate z(r) diverges to +∞ as
r tends to 1 from below. This is not an assumed endpoint map. -/
theorem quarticZ_tendsto_atTop :
    Tendsto quarticZ (𝓝[<] (1 : ℝ)) atTop := by
  have hnum :
      Tendsto (fun t : ℝ => Real.sqrt 2 * t)
        (𝓝[<] (1 : ℝ)) (𝓝 (Real.sqrt 2)) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt 2 * t) := by fun_prop
    simpa only [mul_one] using
      (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hden :
      Tendsto (fun t : ℝ => 1 - t ^ 2)
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hc : Continuous (fun t : ℝ => 1 - t ^ 2) := by fun_prop
    simpa only [one_pow, sub_self] using
      (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hbelow :
      ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), t < 1 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ht
  have habove :
      ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 0 < t := by
    exact nhdsWithin_le_nhds
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hpos :
      ∀ᶠ t : ℝ in 𝓝[<] (1 : ℝ), 0 < 1 - t ^ 2 := by
    filter_upwards [hbelow, habove] with t ht h0
    have hh : 0 < (1 - t) * (1 + t) := by
      apply mul_pos
      · linarith
      · linarith
    nlinarith
  have hdenGT :
      Tendsto (fun t : ℝ => 1 - t ^ 2)
        (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hden hpos
  have hinv :
      Tendsto (fun t : ℝ => (1 - t ^ 2)⁻¹)
        (𝓝[<] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp hdenGT
  have hmul := Filter.Tendsto.atTop_mul_pos
    (show 0 < Real.sqrt (2 : ℝ) by positivity) hinv hnum
  convert hmul using 1
  funext t
  unfold quarticZ
  ring

/-- Full analytic period equation (555), with ordinary Bochner/
Lebesgue integral on (0,+∞) on the left, and the finite endpoint
integral from 0 to 1 on the right. No abstract period axioms,
invented integrability, or formal symbolic limits are used. -/
theorem complete_quartic_elliptic_period_identity :
    (∫ z in Ioi (0 : ℝ), targetIntegrand z) =
      ∫ t in (0 : ℝ)..1, sourceIntegrand t := by
  have htargetLimit :
      Tendsto
        (fun r : ℝ => ∫ z in (0 : ℝ)..quarticZ r, targetIntegrand z)
        (𝓝[<] (1 : ℝ))
        (𝓝 (∫ z in Ioi (0 : ℝ), targetIntegrand z)) :=
    intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      targetIntegrand_integrable.integrableOn quarticZ_tendsto_atTop
  have hsourceLimit :
      Tendsto
        (fun r : ℝ => ∫ t in (0 : ℝ)..r, sourceIntegrand t)
        (𝓝[<] (1 : ℝ))
        (𝓝 (∫ t in (0 : ℝ)..1, sourceIntegrand t)) := by
    have hcont := intervalIntegral.continuous_primitive
      (μ := volume)
      (fun a b => sourceIntegrand_continuous.intervalIntegrable a b)
      (0 : ℝ)
    exact (hcont.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hbelow :
      ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), r < 1 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact hr
  have habove :
      ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r := by
    have hgt :
        ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r :=
      nhdsWithin_le_nhds
        (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    exact hgt.mono (fun _ h => h.le)
  have hEq :
      (fun r : ℝ => ∫ z in (0 : ℝ)..quarticZ r, targetIntegrand z)
        =ᶠ[𝓝[<] (1 : ℝ)]
      (fun r : ℝ => ∫ t in (0 : ℝ)..r, sourceIntegrand t) := by
    filter_upwards [hbelow, habove] with r hr h0
    exact finite_elliptic_period_change_of_variables r h0 hr
  exact tendsto_nhds_unique (htargetLimit.congr' hEq) hsourceLimit

#print axioms Manuscript15.CrossQuarticImproperPeriod20261125.sourceIntegrand_continuous
#print axioms Manuscript15.CrossQuarticImproperPeriod20261125.targetIntegrand_continuous
#print axioms Manuscript15.CrossQuarticImproperPeriod20261125.targetIntegrand_norm_bound
#print axioms Manuscript15.CrossQuarticImproperPeriod20261125.targetIntegrand_integrable
#print axioms Manuscript15.CrossQuarticImproperPeriod20261125.quarticZ_tendsto_atTop
#print axioms Manuscript15.CrossQuarticImproperPeriod20261125.complete_quartic_elliptic_period_identity

end Manuscript15.CrossQuarticImproperPeriod20261125
