import Manuscript15.EulerianConvolutionCharacteristicPowers
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Manuscript 15 — dense-frequency uniqueness for every genuine Eulerian convolution law

Let μ_E be the actual centered uniform Borel probability measure, and
let μ_E^{∗n} denote its n-fold additive convolution (including Dirac at
zero for n=0). The all-order Fourier identity for these actual measures
is established in EulerianConvolutionCharacteristicPowers.

A finite Borel measure ν whose complex characteristic function equals
the n-th Eulerian sinc power on ANY dense set of real frequencies
must be exactly μ_E^{∗n}. This is a direct application of the
continuous characteristic function and Fourier injectivity theorem
already formalized in Mathlib; it does not assume moments or density
regularity of ν.

This theorem does not claim an analytic rigidity characterization of
the Eulerian profile from an unrelated geometric equation.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Set Topology

/-- For every convolution order n, values of the complex characteristic
function on any dense frequency set determine the genuine n-fold
Eulerian uniform convolution among all finite Borel measures. -/
theorem finiteMeasure_eq_eulerianConvolutionPower_of_charFun_eqOn_dense
    (n : ℕ) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (s : Set ℝ) (hs : Dense s)
    (h : ∀ t ∈ s,
      charFun ν t = (EulerianCert.FourierModes.rE t : ℂ) ^ n) :
    ν = eulerianConvolutionPower n := by
  letI : IsProbabilityMeasure (eulerianConvolutionPower n) :=
    eulerianConvolutionPower_isProbability n
  have hfun : charFun ν = charFun (eulerianConvolutionPower n) :=
    Continuous.ext_on hs
      (continuous_charFun (μ := ν))
      (continuous_charFun (μ := eulerianConvolutionPower n))
      (fun t ht => (h t ht).trans
        (eulerianConvolutionPower_charFun n t).symm)
  exact Measure.ext_of_charFun hfun

#print axioms Manuscript15.finiteMeasure_eq_eulerianConvolutionPower_of_charFun_eqOn_dense

end Manuscript15
