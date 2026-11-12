import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Manuscript 15 — characteristic-function uniqueness of probability measures

This module isolates a rigorously existing Mathlib prerequisite for
probabilistic reconstruction. By the Lévy continuity theorem, if two
probability measures on a finite-dimensional real inner-product space
have identical characteristic functions at every point, then the
two probability measures themselves are identical.

The proof is the constant-sequence specialization of Mathlib's
ProbabilityMeasure.tendsto_of_tendsto_charFun, using uniqueness
of limits in the Hausdorff weak topology on probability measures.

The classical Lévy theorem is not new. What is established here is
an explicitly Lean-certified uniqueness interface for Manuscript 15:
AFTER an analytic/geometric argument identifies the Fourier
characteristic function of a candidate probability measure, the
measure itself is uniquely determined. The separate identification
of Eulerian rE with a particular measure's characteristic function
remains an independent proof obligation.
-/

noncomputable section

namespace Manuscript15

open Filter MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Classical Lévy-based injectivity of the characteristic function
on ALL probability measures of any finite-dimensional real
inner-product space, proved from convergence of a constant sequence. -/
theorem probabilityMeasure_eq_of_charFun_eq
    (μ ν : ProbabilityMeasure E)
    (h : ∀ t : E, charFun μ t = charFun ν t) :
    μ = ν := by
  have hconv :
      Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    simpa only [h t] using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => charFun ν t)
          atTop (𝓝 (charFun ν t)))
  exact tendsto_nhds_unique tendsto_const_nhds hconv

/-- One-dimensional real specialization used for Eulerian
characteristic-function and probabilistic reconstruction. -/
theorem real_probabilityMeasure_eq_of_charFun_eq
    (μ ν : ProbabilityMeasure ℝ)
    (h : ∀ t : ℝ, charFun μ t = charFun ν t) :
    μ = ν :=
  probabilityMeasure_eq_of_charFun_eq μ ν h

#print axioms Manuscript15.probabilityMeasure_eq_of_charFun_eq
#print axioms Manuscript15.real_probabilityMeasure_eq_of_charFun_eq

end Manuscript15
