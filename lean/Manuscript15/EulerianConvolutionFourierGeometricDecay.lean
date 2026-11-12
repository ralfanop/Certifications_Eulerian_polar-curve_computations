import Manuscript15.EulerianConvolutionDistinctOrders
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Manuscript 15 — quantitative geometric Fourier decay of uniform convolution

For the genuine centered-uniform probability law μ_E and its actual
n-fold additive convolution, the Eulerian characteristic function at
frequency π is exactly (2/π)^n.

Since 0 < 2/π < 1, the real spectral value is strictly decreasing with
the number of convolutions and converges geometrically to zero. Both
results concern actual Borel probability distributions, not a formal
algebraic family of sinc powers.

The limit is a fixed-frequency characteristic-value limit. It does NOT
assert weak convergence of the probability measures to an improper
zero measure or a normal law.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Filter Topology

/-- At the fixed nonzero frequency π, the real characteristic
value of genuine n-fold Eulerian uniform convolution is strictly
decreasing as the natural-number convolution order increases. -/
theorem eulerianConvolutionPower_charFun_pi_real_strictAnti :
    StrictAnti
      (fun n : ℕ => (charFun (eulerianConvolutionPower n) Real.pi).re) := by
  have hpos : 0 < (2 / Real.pi : ℝ) :=
    div_pos (by norm_num) Real.pi_pos
  have hlt : (2 / Real.pi : ℝ) < 1 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  intro m n hmn
  have h := (pow_right_strictAnti₀ hpos hlt) hmn
  simpa only [eulerianConvolutionPower_charFun_pi,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

/-- The actual n-fold Eulerian convolution characteristic function
decays geometrically to zero at the fixed Fourier frequency π. -/
theorem eulerianConvolutionPower_charFun_pi_real_tendsto_zero :
    Tendsto
      (fun n : ℕ => (charFun (eulerianConvolutionPower n) Real.pi).re)
      atTop (𝓝 (0 : ℝ)) := by
  have hpos : 0 ≤ (2 / Real.pi : ℝ) :=
    (div_pos (by norm_num) Real.pi_pos).le
  have hlt : (2 / Real.pi : ℝ) < 1 := by
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have h : Tendsto (fun n : ℕ => (2 / Real.pi : ℝ) ^ n)
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hpos hlt
  simpa only [eulerianConvolutionPower_charFun_pi,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

#print axioms Manuscript15.eulerianConvolutionPower_charFun_pi_real_strictAnti
#print axioms Manuscript15.eulerianConvolutionPower_charFun_pi_real_tendsto_zero

end Manuscript15
