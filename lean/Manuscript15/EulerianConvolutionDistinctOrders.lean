import Manuscript15.EulerianConvolutionDenseIdentification
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# Manuscript 15 — distinctness of all Eulerian uniform convolution orders

Let μ_E denote the actual centered uniform probability measure on
[-1/2,1/2] and let μ_E^{∗n} be its genuine n-fold additive convolution,
with μ_E^{∗0} equal to the Dirac mass at zero.

The previously established, fully formalized characteristic identity
  charFun (μ_E^{∗n})(t) = (r_E(t) : ℂ)^n
allows separation of ANY TWO convolution orders with only a SINGLE
real spectral-frequency measurement at t=π.

Indeed r_E(π)=2/π belongs strictly to (0,1). Its powers therefore
form a strictly decreasing sequence, so equality of the actual Borel
probability laws implies equality of the convolution orders.

No assumptions of a density, absolute continuity, variance, or
moments are used. This avoids a circular dependence on any
not-yet-certified probabilistic moment-convolution formula.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory

/-- The exact characteristic function of the actual n-fold Eulerian
uniform convolution at the single distinguished frequency π. -/
theorem eulerianConvolutionPower_charFun_pi (n : ℕ) :
    charFun (eulerianConvolutionPower n) Real.pi =
      (((2 / Real.pi : ℝ) : ℂ) ^ n) := by
  simpa only [EulerianCert.FourierModes.rE_pi] using
    eulerianConvolutionPower_charFun n Real.pi

/-- All genuine n-fold Eulerian centered-uniform convolution
probability laws are pairwise distinct, including the zero-fold
Dirac distribution. In fact their complex characteristic values
at frequency π alone distinguish their natural-number orders. -/
theorem eulerianConvolutionPower_injective :
    Function.Injective eulerianConvolutionPower := by
  intro m n hmn
  have hrpos : 0 < EulerianCert.FourierModes.rE Real.pi := by
    rw [EulerianCert.FourierModes.rE_pi]
    exact div_pos (by norm_num) Real.pi_pos
  have hrlt : EulerianCert.FourierModes.rE Real.pi < 1 := by
    rw [EulerianCert.FourierModes.rE_pi]
    apply (div_lt_iff₀ Real.pi_pos).2
    linarith [Real.pi_gt_three]
  have hchar :
      (EulerianCert.FourierModes.rE Real.pi : ℂ) ^ m =
        (EulerianCert.FourierModes.rE Real.pi : ℂ) ^ n := by
    calc
      (EulerianCert.FourierModes.rE Real.pi : ℂ) ^ m =
          charFun (eulerianConvolutionPower m) Real.pi :=
        (eulerianConvolutionPower_charFun m Real.pi).symm
      _ = charFun (eulerianConvolutionPower n) Real.pi := by rw [hmn]
      _ = (EulerianCert.FourierModes.rE Real.pi : ℂ) ^ n :=
        eulerianConvolutionPower_charFun n Real.pi
  have hreal :
      EulerianCert.FourierModes.rE Real.pi ^ m =
        EulerianCert.FourierModes.rE Real.pi ^ n := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow] using hchar
  exact (pow_right_injective₀ hrpos (ne_of_lt hrlt)) hreal

/-- Equality of two genuine Eulerian centered-uniform convolution laws
is equivalent to equality of their convolution orders. -/
theorem eulerianConvolutionPower_eq_iff (m n : ℕ) :
    eulerianConvolutionPower m = eulerianConvolutionPower n ↔ m = n :=
  eulerianConvolutionPower_injective.eq_iff

#print axioms Manuscript15.eulerianConvolutionPower_charFun_pi
#print axioms Manuscript15.eulerianConvolutionPower_injective
#print axioms Manuscript15.eulerianConvolutionPower_eq_iff

end Manuscript15
