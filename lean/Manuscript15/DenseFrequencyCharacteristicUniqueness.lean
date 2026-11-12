import Manuscript15.CharacteristicMeasureUniqueness
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Separation.Hausdorff

/-!
# Manuscript 15 — uniqueness from characteristic data on a dense frequency set

For arbitrary finite Borel measures μ, ν on a complete, second-countable
real inner-product space E, it is not necessary to match characteristic
functions at every frequency a priori. Their equality on any DENSE
frequency set suffices to identify the entire measures exactly.

The proof uses the classical Mathlib continuous_charFun theorem (which
requires only finiteness, not existence of higher moments), extends
equality from a dense subset by continuity, and applies the classical
measure-extensionality theorem Measure.ext_of_charFun.

This allows an analytic reconstruction argument in Manuscript 15
to establish an identity only on a dense subset of real frequencies
before concluding uniqueness of the probability measure, once
existence of a candidate measure has separately been proved.

No claim is made that the Eulerian sinc is the characteristic function
of the proposed measure here; that identity remains separate.
-/

noncomputable section

namespace Manuscript15

open MeasureTheory Set Topology

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- A finite Borel measure on a complete, second-countable Hilbert
space is uniquely determined by the values of its complex
characteristic function on ANY dense set of frequencies. -/
theorem finiteMeasure_eq_of_charFun_eqOn_dense
    (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set E) (hs : Dense s)
    (h : EqOn (charFun μ) (charFun ν) s) :
    μ = ν := by
  have hfunctions : charFun μ = charFun ν :=
    Continuous.ext_on hs
      (continuous_charFun (μ := μ))
      (continuous_charFun (μ := ν)) h
  exact Measure.ext_of_charFun hfunctions

/-- One-dimensional version for the characteristic measures relevant
to Eulerian probability and cycloidal reconstruction. -/
theorem real_finiteMeasure_eq_of_charFun_eqOn_dense
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (s : Set ℝ) (hs : Dense s)
    (h : EqOn (charFun μ) (charFun ν) s) :
    μ = ν :=
  finiteMeasure_eq_of_charFun_eqOn_dense μ ν s hs h

#print axioms Manuscript15.finiteMeasure_eq_of_charFun_eqOn_dense
#print axioms Manuscript15.real_finiteMeasure_eq_of_charFun_eqOn_dense

end Manuscript15
