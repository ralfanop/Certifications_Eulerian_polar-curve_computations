import Manuscript15.UniformEulerianCharacteristicMeasure
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Manuscript 15 — exact uniqueness of the uniform Eulerian characteristic measure

The previous module constructs the ACTUAL Borel probability measure
  μ_E = volume.restrict (Icc (-1/2) (1/2))
and rigorously identifies its complex characteristic function:
  charFun μ_E(t) = rE(t) = sinc(t/2)
for every real frequency t, including t=0.

We now close the independent classical uniqueness obligation at the
MEASURE LEVEL: any finite Borel measure with characteristic function
equal to rE at every real t is exactly μ_E. Indeed it is sufficient
to establish that identity only on a DENSE subset of real frequencies.

The result is a direct, exact use of the classical Mathlib Fourier
measure-extensionality theorem and continuity of finite-measure
characteristic functions. It is not an assertion that a geometric
functional equation has been proved to force this characteristic
function; the analytic rigidity implication is a separate obligation.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Set Topology

/-- The actual Eulerian sinc profile uniquely determines its
centered uniform probability measure: among ALL finite Borel
measures on ℝ, there is no other with the same entire characteristic
function. -/
theorem finiteMeasure_eq_eulerianUniform_of_charFun
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (h : ∀ t : ℝ,
      charFun μ t = (EulerianCert.FourierModes.rE t : ℂ)) :
    μ = eulerianUniformMeasure := by
  apply Measure.ext_of_charFun
  funext t
  exact (h t).trans (eulerianUniformMeasure_charFun t).symm

/-- Stronger practical criterion: equality with the Eulerian sinc
profile on ANY dense real frequency subset uniquely determines the
actual centered uniform measure, even among general finite measures,
without requiring the existence of a first or higher moment. -/
theorem finiteMeasure_eq_eulerianUniform_of_charFun_eqOn_dense
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (s : Set ℝ) (hs : Dense s)
    (h : ∀ t ∈ s,
      charFun μ t = (EulerianCert.FourierModes.rE t : ℂ)) :
    μ = eulerianUniformMeasure := by
  have hfun : charFun μ = charFun eulerianUniformMeasure :=
    Continuous.ext_on hs
      (continuous_charFun (μ := μ))
      (continuous_charFun (μ := eulerianUniformMeasure))
      (fun t ht => (h t ht).trans
        (eulerianUniformMeasure_charFun t).symm)
  exact Measure.ext_of_charFun hfun

#print axioms Manuscript15.finiteMeasure_eq_eulerianUniform_of_charFun
#print axioms Manuscript15.finiteMeasure_eq_eulerianUniform_of_charFun_eqOn_dense

end Manuscript15
