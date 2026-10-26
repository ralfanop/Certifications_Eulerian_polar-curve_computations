import GegenbauerFock.GramMomentIntegralSeries

/-!
# V007: absolute summability of the full analytic adjoint power-series weights

This supplies the precise ℓ² × ℓ² Hölder bound needed to upgrade
the L² Hilbert-adjoint series into a pointwise absolutely convergent
analytic restriction, uniformly on the ultraspherical support.
-/

open scoped ENNReal

namespace GegenbauerFock.AdjointSummability

/-- Actual ℓ² sequence of all conjugated-Fourier-series amplitudes. -/
noncomputable def fockWeightVector (alpha : ℝ) (ha : 0 < alpha) :
    InfiniteAnalysis.FockCoefficients :=
  ⟨WeightedMoments.complexWeight alpha, by
    apply memℓp_gen
    have hs : Summable (fun n : ℕ =>
        ‖WeightedMoments.complexWeight alpha n‖ ^ 2) := by
      simpa only [WeightedMoments.complexWeight_norm_sq alpha ha] using
        (WeightedMoments.squareWeight_summable alpha)
    simpa using hs⟩

/-- The coefficient magnitudes of the analytic adjoint series form
a genuinely summable sequence for each arbitrary Fock vector F. -/
theorem summable_weighted_coefficients
    (alpha : ℝ) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    Summable (fun n : ℕ =>
      ‖F n‖ * ‖WeightedMoments.complexWeight alpha n‖) := by
  have htriple : (2 : ℝ≥0∞).HolderTriple 2 1 := by
    rw [ENNReal.holderTriple_iff]
    norm_num
  letI : (2 : ℝ≥0∞).HolderTriple 2 1 := htriple
  have hholder : ((2 : ℝ≥0∞).toReal).HolderConjugate
      ((2 : ℝ≥0∞).toReal) := by
    norm_num [Real.HolderConjugate]
  simpa only [fockWeightVector] using
    (lp.summable_mul hholder F (fockWeightVector alpha ha))

#print axioms GegenbauerFock.AdjointSummability.summable_weighted_coefficients

end GegenbauerFock.AdjointSummability
