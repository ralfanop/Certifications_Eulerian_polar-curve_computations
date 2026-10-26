import GegenbauerFock.GramIntegralKernel

/-!
# V007: actual analytic point-evaluation restriction along the imaginary axis

This module proves measurability of the reconstructed Fock evaluation
on the imaginary line, and prepares its L² interpretation independently
of the Hilbert adjoint. No pointwise representative is assigned to
an arbitrary L² equivalence class.
-/

open MeasureTheory
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockAnalyticRestriction

/-- The imaginary point corresponding to a real ultraspherical coordinate. -/
noncomputable def imaginaryPoint (alpha : ℝ) (u : ℝ) : ℂ :=
  -Complex.I * (u : ℂ) / (2 * (alpha : ℂ))

/-- Pointwise reconstruction of the analytic Fock coefficient vector,
restricted to the imaginary axis at w=-i*u/(2α). -/
noncomputable def evaluate (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) (u : ℝ) : ℂ :=
  FockEvaluation.evaluation alpha ha (imaginaryPoint alpha u) F

/-- The analytic restriction is a measurable complex-valued function
of u, for an arbitrary infinite Fock vector. -/
theorem measurable_evaluate (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    Measurable (evaluate alpha ha F) := by
  have hterm (n : ℕ) :
      Measurable (fun u : ℝ =>
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) := by
    have hc : Continuous (fun u : ℝ =>
        inner ℂ
          (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
          (F n)) := by
      unfold imaginaryPoint FockEvaluation.kernelCoordinate
      fun_prop
    exact hc.measurable
  have heq :
      evaluate alpha ha F =
        fun u : ℝ => ∑' n : ℕ,
          inner ℂ
            (FockEvaluation.kernelCoordinate alpha (imaginaryPoint alpha u) n)
            (F n) := by
    funext u
    exact FockEvaluation.evaluation_eq_tsum_inner
      alpha ha (imaginaryPoint alpha u) F
  rw [heq]
  exact Measurable.tsum hterm

#print axioms GegenbauerFock.FockAnalyticRestriction.measurable_evaluate

end GegenbauerFock.FockAnalyticRestriction
