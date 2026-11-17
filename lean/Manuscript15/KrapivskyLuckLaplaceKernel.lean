import Manuscript15.KrapivskyLuckMobiusBridge

/-! Actual analytic kernel of M15 eq:stirling-spectral-expansion and
M14 det-mobius. Follow-up to #327: prove the summability hypothesis,
rather than assuming it. Binet's formula and evaluation of the surviving
integral are distinct obligations. -/

open MeasureTheory Set Real ArithmeticFunction
open scoped BigOperators

noncomputable section

namespace Manuscripts14And15.KrapivskyLuck

def laplaceIntegrand (m : ℕ) (u : ℝ) : ℝ :=
  Real.exp (-u) / (u^2 + 4 * Real.pi^2 * (m : ℝ)^2)

def laplaceKernel (m : ℕ) : ℝ :=
  if m = 0 then 0 else 2 * ∫ u : ℝ in Ioi 0, laplaceIntegrand m u

theorem laplaceIntegrand_nonneg (m : ℕ) (u : ℝ) :
    0 ≤ laplaceIntegrand m u := by
  unfold laplaceIntegrand
  positivity

theorem laplaceIntegrand_dom (m : ℕ) (hm : m ≠ 0) (u : ℝ) :
    laplaceIntegrand m u ≤
      (1 / (4 * Real.pi^2 * (m : ℝ)^2)) * Real.exp (-u) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hd : 0 < 4 * Real.pi^2 * (m : ℝ)^2 := by positivity
  unfold laplaceIntegrand
  calc
    _ ≤ Real.exp (-u) / (4 * Real.pi^2 * (m : ℝ)^2) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le hd (by nlinarith [sq_nonneg u])
    _ = _ := by ring

theorem laplaceIntegrand_integrable (m : ℕ) (hm : m ≠ 0) :
    IntegrableOn (laplaceIntegrand m) (Ioi 0) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hc : Continuous (laplaceIntegrand m) := by
    unfold laplaceIntegrand
    apply (Real.continuous_exp.comp continuous_neg).div (by fun_prop)
    intro u
    exact ne_of_gt (by positivity)
  have hdom := (integrableOn_exp_neg_Ioi 0).const_mul
    (1 / (4 * Real.pi^2 * (m : ℝ)^2))
  exact hdom.mono_nonneg hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (laplaceIntegrand_nonneg m))
    (Filter.Eventually.of_forall (laplaceIntegrand_dom m hm))

theorem laplaceKernel_nonneg (m : ℕ) : 0 ≤ laplaceKernel m := by
  by_cases hm : m = 0
  · simp [laplaceKernel, hm]
  · rw [laplaceKernel, if_neg hm]
    exact mul_nonneg (by norm_num) (integral_nonneg (laplaceIntegrand_nonneg m))

theorem laplaceKernel_bound (m : ℕ) :
    laplaceKernel m ≤ (2 / (4 * Real.pi^2)) * (1 / (m : ℝ)^2) := by
  by_cases hm : m = 0
  · simp [laplaceKernel, hm]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hdom := (integrableOn_exp_neg_Ioi 0).const_mul
    (1 / (4 * Real.pi^2 * (m : ℝ)^2))
  have h := integral_mono (laplaceIntegrand_integrable m hm) hdom
    (laplaceIntegrand_dom m hm)
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one] at h
  rw [laplaceKernel, if_neg hm]
  calc
    _ ≤ 2 * (1 / (4 * Real.pi^2 * (m : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by field_simp [Real.pi_ne_zero, hm'] <;> ring

private theorem product_majorant_summable :
    Summable (fun p : ℕ × ℕ =>
      (1 / (p.1 : ℝ)^2) * (1 / (p.2 : ℝ)^2)) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply (summable_prod_of_nonneg (fun p => by positivity)).2
  constructor
  · intro n
    change Summable (fun y : ℕ => (1 / (n : ℝ)^2) * (1 / (y : ℝ)^2))
    exact hs.mul_left (1 / (n : ℝ)^2)
  · simp_rw [tsum_mul_left]
    exact hs.mul_right _

theorem laplaceKernel_abs_summable :
    Summable (fun p : ℕ × ℕ =>
      ‖(↑(moebius p.1) : ℝ) * laplaceKernel (p.1 * p.2)‖) := by
  have hs := product_majorant_summable.mul_left (2 / (4 * Real.pi^2))
  apply hs.of_norm_bounded
  intro p
  simp only [Real.norm_eq_abs, abs_abs, abs_mul, abs_of_nonneg (laplaceKernel_nonneg _)]
  have hμ : |(↑(moebius p.1) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := p.1))
  calc
    _ ≤ 1 * laplaceKernel (p.1 * p.2) :=
      mul_le_mul_of_nonneg_right hμ (laplaceKernel_nonneg _)
    _ = laplaceKernel (p.1 * p.2) := one_mul _
    _ ≤ (2 / (4 * Real.pi^2)) * (1 / ((p.1 * p.2 : ℕ) : ℝ)^2) :=
      laplaceKernel_bound _
    _ = _ := by
      rw [Nat.cast_mul]
      by_cases h1 : (p.1 : ℝ) = 0
      · simp [h1]
      by_cases h2 : (p.2 : ℝ) = 0
      · simp [h2]
      field_simp [Real.pi_ne_zero, h1, h2] <;> ring

theorem laplaceKernel_mobius_cancellation :
    (∑' p : ℕ × ℕ, (↑(moebius p.1) : ℝ) * laplaceKernel (p.1 * p.2)) =
      2 * ∫ u : ℝ in Ioi 0, Real.exp (-u) / (u^2 + 4 * Real.pi^2) := by
  have hs := laplaceKernel_abs_summable.of_norm
  rw [mobius_kernel_tsum laplaceKernel (by simp [laplaceKernel]) hs]
  simp [laplaceKernel, laplaceIntegrand]

end Manuscripts14And15.KrapivskyLuck

#print axioms Manuscripts14And15.KrapivskyLuck.laplaceIntegrand_nonneg
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceIntegrand_dom
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceIntegrand_integrable
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceKernel_nonneg
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceKernel_bound
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceKernel_abs_summable
#print axioms Manuscripts14And15.KrapivskyLuck.laplaceKernel_mobius_cancellation
