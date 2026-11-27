import Mathlib
import Manuscript13.EllisComplexResolvent20261127
open MeasureTheory Set Filter
namespace Manuscript13.EllisGreenKernel20261127
noncomputable section
open Manuscript13.EllisComplexResolvent20261127
/-! Actual Green function and its Fourier integral in cycles.
The L¹ convolution theorem extended to L² and the identification
with the weighted Gram operator are subsequent obligations. -/
def green (κ t : ℝ) : ℂ := (Real.exp (-κ * |t|) / (2*κ) : ℝ)

def ratePlus (κ ξ : ℝ) : ℂ := -(κ : ℂ) - (2*Real.pi*ξ : ℝ) * Complex.I
def rateMinus (κ ξ : ℝ) : ℂ := (κ : ℂ) - (2*Real.pi*ξ : ℝ) * Complex.I

def integrand (κ ξ t : ℝ) : ℂ :=
  green κ t * Complex.exp (-(2*Real.pi*ξ*t : ℝ) * Complex.I)

theorem positive_half (κ ξ t : ℝ) (ht : 0 ≤ t) :
    integrand κ ξ t = (1 / (2*(κ : ℂ))) * Complex.exp (ratePlus κ ξ * t) := by
  unfold integrand green ratePlus
  rw [abs_of_nonneg ht]
  push_cast
  rw [Complex.ofReal_exp]
  have h : (-(κ : ℂ) - (2*Real.pi*ξ : ℝ)*Complex.I)*t =
      ((-κ*t : ℝ) : ℂ) + -((2*Real.pi*ξ*t : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [h, Complex.exp_add]
  push_cast
  ring

theorem negative_half (κ ξ t : ℝ) (ht : t ≤ 0) :
    integrand κ ξ t = (1 / (2*(κ : ℂ))) * Complex.exp (rateMinus κ ξ * t) := by
  unfold integrand green rateMinus
  rw [abs_of_nonpos ht]
  push_cast
  rw [Complex.ofReal_exp]
  have h : ((κ : ℂ) - (2*Real.pi*ξ : ℝ)*Complex.I)*t =
      ((-κ*(-t) : ℝ) : ℂ) + -((2*Real.pi*ξ*t : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [h, Complex.exp_add]
  push_cast
  ring

theorem ratePlus_re (κ ξ : ℝ) : (ratePlus κ ξ).re = -κ := by
  simp [ratePlus, Complex.mul_re]
theorem rateMinus_re (κ ξ : ℝ) : (rateMinus κ ξ).re = κ := by
  simp [rateMinus, Complex.mul_re]

theorem positive_integrable (κ ξ : ℝ) (hk : 0 < κ) :
    IntegrableOn (integrand κ ξ) (Ioi 0) := by
  have hr : (ratePlus κ ξ).re < 0 := by rw [ratePlus_re]; linarith
  apply ((integrableOn_exp_mul_complex_Ioi hr 0).const_mul (1/(2*(κ:ℂ)))).congr_fun
  · intro t ht
    exact (positive_half κ ξ t (le_of_lt ht)).symm
  · exact measurableSet_Ioi

theorem negative_integrable (κ ξ : ℝ) (hk : 0 < κ) :
    IntegrableOn (integrand κ ξ) (Iic 0) := by
  have hr : 0 < (rateMinus κ ξ).re := by rw [rateMinus_re]; exact hk
  apply ((integrableOn_exp_mul_complex_Iic hr 0).const_mul (1/(2*(κ:ℂ)))).congr_fun
  · intro t ht
    exact (negative_half κ ξ t ht).symm
  · exact measurableSet_Iic

theorem positive_integral (κ ξ : ℝ) (hk : 0 < κ) :
    (∫ t in Ioi (0:ℝ), integrand κ ξ t) =
      (1/(2*(κ:ℂ))) * (-(1:ℂ)/ratePlus κ ξ) := by
  have hr : (ratePlus κ ξ).re < 0 := by rw [ratePlus_re]; linarith
  calc
    _ = ∫ t in Ioi (0:ℝ), (1/(2*(κ:ℂ))) * Complex.exp (ratePlus κ ξ*t) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact positive_half κ ξ t (le_of_lt ht)
    _ = _ := by rw [integral_const_mul, integral_exp_mul_complex_Ioi hr]; simp

theorem negative_integral (κ ξ : ℝ) (hk : 0 < κ) :
    (∫ t in Iic (0:ℝ), integrand κ ξ t) =
      (1/(2*(κ:ℂ))) * (1/rateMinus κ ξ) := by
  have hr : 0 < (rateMinus κ ξ).re := by rw [rateMinus_re]; exact hk
  calc
    _ = ∫ t in Iic (0:ℝ), (1/(2*(κ:ℂ))) * Complex.exp (rateMinus κ ξ*t) := by
      apply setIntegral_congr_fun measurableSet_Iic
      intro t ht
      exact negative_half κ ξ t ht
    _ = _ := by rw [integral_const_mul, integral_exp_mul_complex_Iic hr]; simp

theorem halfline_sum (κ ξ : ℝ) (hk : 0 < κ) :
    (1/(2*(κ:ℂ))) * (-(1:ℂ)/ratePlus κ ξ) +
    (1/(2*(κ:ℂ))) * (1/rateMinus κ ξ) = multiplier κ ξ := by
  have hp : ratePlus κ ξ ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    rw [ratePlus_re] at he
    simp at he
    linarith
  have hm : rateMinus κ ξ ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    rw [rateMinus_re] at he
    simp at he
    linarith
  have hs : (symbol κ ξ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (symbol_pos κ ξ hk)
  have hκ : (κ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hk
  unfold multiplier
  push_cast
  field_simp [hp,hm,hs,hκ]
  unfold ratePlus rateMinus symbol
  push_cast
  ring_nf
  simp [Complex.I_sq]
  <;> ring

theorem green_fourier_integral (κ ξ : ℝ) (hk : 0 < κ) :
    (∫ t : ℝ, integrand κ ξ t) = multiplier κ ξ := by
  have hpos := positive_integrable κ ξ hk
  have hneg := negative_integrable κ ξ hk
  have hi : Integrable (integrand κ ξ) := by
    have h := hneg.union hpos
    rw [Iic_union_Ioi] at h
    simpa using h
  calc
    _ = (∫ t in Iic (0:ℝ), integrand κ ξ t) +
        (∫ t in Ioi (0:ℝ), integrand κ ξ t) := by
      have h := integral_add_compl measurableSet_Iic hi
      simpa only [compl_Iic] using h.symm
    _ = _ := by rw [negative_integral κ ξ hk,positive_integral κ ξ hk,add_comm]; exact halfline_sum κ ξ hk

theorem green_even (κ t : ℝ) : green κ (-t) = green κ t := by simp [green]
end
end Manuscript13.EllisGreenKernel20261127
#print axioms Manuscript13.EllisGreenKernel20261127.green
#print axioms Manuscript13.EllisGreenKernel20261127.ratePlus
#print axioms Manuscript13.EllisGreenKernel20261127.rateMinus
#print axioms Manuscript13.EllisGreenKernel20261127.integrand
#print axioms Manuscript13.EllisGreenKernel20261127.positive_half
#print axioms Manuscript13.EllisGreenKernel20261127.negative_half
#print axioms Manuscript13.EllisGreenKernel20261127.ratePlus_re
#print axioms Manuscript13.EllisGreenKernel20261127.rateMinus_re
#print axioms Manuscript13.EllisGreenKernel20261127.positive_integrable
#print axioms Manuscript13.EllisGreenKernel20261127.negative_integrable
#print axioms Manuscript13.EllisGreenKernel20261127.positive_integral
#print axioms Manuscript13.EllisGreenKernel20261127.negative_integral
#print axioms Manuscript13.EllisGreenKernel20261127.halfline_sum
#print axioms Manuscript13.EllisGreenKernel20261127.green_fourier_integral
#print axioms Manuscript13.EllisGreenKernel20261127.green_even
