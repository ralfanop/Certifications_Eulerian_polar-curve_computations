import Manuscript15.KrapivskyLuckDampedTail
import Manuscript15.KrapivskyLuckSpectralIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! M15 §6.6: actual integrability, interchange and evaluation of the
nonnegative damped cosine kernel. No Binet/Gamma-log identification or
Plancherel hypothesis is asserted here. -/

open MeasureTheory Set Real ArithmeticFunction
open scoped BigOperators
noncomputable section
namespace Manuscripts14And15.KrapivskyLuck

theorem gamma2_integral :
    (∫ u : ℝ in Ioi 0, u * Real.exp (-u)) = 1 := by
  have h := Real.Gamma_eq_integral (s := 2) (by norm_num)
  have h2 : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  rw [h2] at h
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm] using h.symm

theorem gamma2_scaled_integral (t : ℝ) (ht : 0 < t) :
    (∫ s : ℝ in Ioi 0, s * Real.exp (-s*t)) = 1/t^2 := by
  let g : ℝ → ℝ := fun u => u * Real.exp (-u)
  have he : (fun s : ℝ => s * Real.exp (-s*t)) =
      fun s => (1/t) * g (t*s) := by
    funext s
    dsimp [g]
    rw [show -s*t = -(t*s) by ring]
    field_simp [ht.ne'] <;> ring
  rw [he, integral_const_mul, integral_comp_mul_left_Ioi g 0 ht]
  simp only [mul_zero, smul_eq_mul]
  rw [show (∫ u : ℝ in Ioi 0, g u) = 1 from gamma2_integral]
  field_simp [ht.ne'] <;> ring

def dampedEnergyKernel (s t : ℝ) : ℝ :=
  s * Real.exp (-s*t) * (1-Real.cos t)

theorem dampedEnergyKernel_nonneg (s t : ℝ) (hs : 0 ≤ s) :
    0 ≤ dampedEnergyKernel s t := by
  unfold dampedEnergyKernel
  exact mul_nonneg (mul_nonneg hs (Real.exp_pos _).le)
    (sub_nonneg.mpr (Real.cos_le_one t))

theorem dampedEnergyKernel_section_integrable (s : ℝ) (hs : 0 < s) :
    IntegrableOn (dampedEnergyKernel s) (Ioi (2*Real.pi)) := by
  apply integrableOn_Ioi_deriv_of_nonneg'
    (fun t _ => tailPrimitive_deriv s t)
    (fun t _ => dampedEnergyKernel_nonneg s t hs.le)
    (tailPrimitive_tendsto s hs)

theorem dampedEnergyKernel_outer_integrable :
    IntegrableOn (fun s : ℝ => Real.exp (-s*(2*Real.pi))/(s^2+1)) (Ioi 0) := by
  let a : ℝ := 2*Real.pi
  have ha : 0 < a := by dsimp [a]; positivity
  have he : IntegrableOn (fun s : ℝ => Real.exp (-(a*s))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun u : ℝ => Real.exp (-u)) 0 ha).2
      (by simpa using integrableOn_exp_neg_Ioi 0)
  change IntegrableOn (fun s : ℝ => Real.exp (-s*a)/(s^2+1)) (Ioi 0)
  have hc : Continuous (fun s : ℝ => Real.exp (-s*a)/(s^2+1)) :=
    (by fun_prop : Continuous (fun s : ℝ => Real.exp (-s*a))).div
      (by fun_prop) (fun _ => ne_of_gt (by positivity))
  refine he.mono_nonneg hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by positivity)) ?_
  apply Filter.Eventually.of_forall
  intro s
  rw [show -s*a = -(a*s) by ring]
  exact div_le_self (Real.exp_pos _).le (by nlinarith [sq_nonneg s])

/-- The actual two-variable kernel belongs to L¹ of the two restricted
Lebesgue measures; no assumed Fubini hypothesis. -/
theorem dampedEnergyKernel_product_integrable :
    Integrable (Function.uncurry dampedEnergyKernel)
      ((volume.restrict (Ioi (0 : ℝ))).prod
        (volume.restrict (Ioi (2*Real.pi)))) := by
  have hc : Continuous (Function.uncurry dampedEnergyKernel) := by
    unfold Function.uncurry dampedEnergyKernel
    fun_prop
  apply (integrable_prod_iff hc.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    exact dampedEnergyKernel_section_integrable s hs
  · refine dampedEnergyKernel_outer_integrable.congr ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    change Real.exp (-s*(2*Real.pi))/(s^2+1) =
      ∫ t : ℝ in Ioi (2*Real.pi), ‖dampedEnergyKernel s t‖
    rw [← damped_cosine_tail s hs]
    apply integral_congr_ae
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (dampedEnergyKernel_nonneg s t (le_of_lt hs))]
    rfl

/-- Exact evaluation of the unweighted cosine tail, with both integration
orders justified by the genuine product integrability theorem. -/
theorem laplace_energy_tail :
    (∫ t : ℝ in Ioi (2*Real.pi), (1-Real.cos t)/t^2) =
      Real.pi * laplaceKernel 1 := by
  have hleft :
      (∫ t : ℝ in Ioi (2*Real.pi), ∫ s : ℝ in Ioi 0, dampedEnergyKernel s t) =
        ∫ t : ℝ in Ioi (2*Real.pi), (1-Real.cos t)/t^2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have ht' : 0 < t := lt_trans (by positivity : 0 < 2*Real.pi) ht
    have he : (fun s : ℝ => dampedEnergyKernel s t) =
        fun s => (1-Real.cos t) * (s*Real.exp (-s*t)) := by
      funext s
      unfold dampedEnergyKernel
      ring
    rw [he, integral_const_mul, gamma2_scaled_integral t ht']
    ring
  have hright :
      (∫ s : ℝ in Ioi 0, ∫ t : ℝ in Ioi (2*Real.pi), dampedEnergyKernel s t) =
        ∫ s : ℝ in Ioi 0, Real.exp (-(2*Real.pi)*s)/(s^2+1) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with s hs
    simpa only [dampedEnergyKernel, mul_comm s (2*Real.pi), neg_mul] using
      damped_cosine_tail s hs
  rw [← hleft, ← integral_integral_swap dampedEnergyKernel_product_integrable,
    hright, scaled_laplaceKernel_one]

/-- New end-to-end Möbius spectral integral to cosine-energy-tail bridge.
Identification of normalizedSpectralRemainder with the classical Stirling
remainder remains an independent theorem. -/
theorem normalizedSpectralRemainder_mobius_energy :
    (∑' n : ℕ, (↑(moebius n) : ℝ) * normalizedSpectralRemainder n) =
      (1/Real.pi) * ∫ t : ℝ in Ioi (2*Real.pi), (1-Real.cos t)/t^2 := by
  rw [normalizedSpectralRemainder_mobius, laplace_energy_tail]
  have hk : laplaceKernel 1 =
      2 * ∫ u : ℝ in Ioi 0, Real.exp (-u)/(u^2+4*Real.pi^2) := by
    simp [laplaceKernel, laplaceIntegrand]
  rw [hk]
  field_simp [Real.pi_ne_zero] <;> ring

end Manuscripts14And15.KrapivskyLuck

#print axioms Manuscripts14And15.KrapivskyLuck.gamma2_integral
#print axioms Manuscripts14And15.KrapivskyLuck.gamma2_scaled_integral
#print axioms Manuscripts14And15.KrapivskyLuck.dampedEnergyKernel_nonneg
#print axioms Manuscripts14And15.KrapivskyLuck.dampedEnergyKernel_section_integrable
#print axioms Manuscripts14And15.KrapivskyLuck.dampedEnergyKernel_outer_integrable
#print axioms Manuscripts14And15.KrapivskyLuck.dampedEnergyKernel_product_integrable
#print axioms Manuscripts14And15.KrapivskyLuck.laplace_energy_tail
#print axioms Manuscripts14And15.KrapivskyLuck.normalizedSpectralRemainder_mobius_energy
