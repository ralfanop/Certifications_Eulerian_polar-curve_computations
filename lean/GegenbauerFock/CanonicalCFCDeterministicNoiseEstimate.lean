import GegenbauerFock.CanonicalCFCRootOperatorNormReconstructionObstruction

/-!
# V007 — deterministic noise amplification for bounded reconstructions

Every bounded linear reconstructor R of a bounded measurement T obeys
the bias + amplified data-noise inequality. We instantiate it for the
actual Gegenbauer–Fock operator C, its canonical positive CFC polar
root P = CFC.sqrt(C* C), and the true source Gram G = C* C.

The result makes NO claim of a uniform bound on R across regularization
parameters and is consistent with the previously certified universal
operator-norm reconstruction obstruction.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Bias-noise decomposition for any bounded complex-linear forward and
reconstruction operators, with the exact operator norm of the latter. -/
theorem bounded_reconstructor_noise_error_le
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (T : H →L[ℂ] K) (R : K →L[ℂ] H)
    (f : H) (eta : K) :
    ‖R (T f + eta) - f‖ ≤
      ‖R (T f) - f‖ + ‖R‖ * ‖eta‖ := by
  have heq : R (T f + eta) - f = (R (T f) - f) + R eta := by
    rw [map_add]
    abel
  calc
    ‖R (T f + eta) - f‖ = ‖(R (T f) - f) + R eta‖ := by rw [heq]
    _ ≤ ‖R (T f) - f‖ + ‖R eta‖ := norm_add_le _ _
    _ ≤ ‖R (T f) - f‖ + ‖R‖ * ‖eta‖ :=
      add_le_add_right (R.le_opNorm eta) _

private abbrev MeasH (lam : ℝ) := Lp ℂ 2 (Ultraspherical.measure lam)

/-- Actual Fock coefficient data have a sharp deterministic
reconstruction-noise upper bound for any bounded left regularizer. -/
theorem C_noisy_reconstruction_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R : InfiniteAnalysis.FockCoefficients →L[ℂ] MeasH lam)
    (f : MeasH lam) (eta : InfiniteAnalysis.FockCoefficients) :
    ‖R (C lam alpha hlam ha f + eta) - f‖ ≤
      ‖R (C lam alpha hlam ha f) - f‖ + ‖R‖ * ‖eta‖ :=
  bounded_reconstructor_noise_error_le (C lam alpha hlam ha) R f eta

/-- Actual canonical CFC positive Gram square-root data obey the same
deterministic bias-noise estimate without a bounded inverse premise. -/
theorem localCFC_noisy_reconstruction_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R : MeasH lam →L[ℂ] MeasH lam)
    (f eta : MeasH lam) :
    ‖R (localCFCGramSqrt lam alpha hlam ha f + eta) - f‖ ≤
      ‖R (localCFCGramSqrt lam alpha hlam ha f) - f‖ +
        ‖R‖ * ‖eta‖ :=
  bounded_reconstructor_noise_error_le
    (localCFCGramSqrt lam alpha hlam ha) R f eta

/-- Source-Gram measurement data obey the deterministic bias-noise
estimate for every bounded linear reconstructor. -/
theorem sourceGram_noisy_reconstruction_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (R : MeasH lam →L[ℂ] MeasH lam)
    (f eta : MeasH lam) :
    ‖R (gram lam alpha hlam ha f + eta) - f‖ ≤
      ‖R (gram lam alpha hlam ha f) - f‖ + ‖R‖ * ‖eta‖ :=
  bounded_reconstructor_noise_error_le
    (gram lam alpha hlam ha) R f eta

#print axioms GegenbauerFock.GeneralUltrasphericalFock.bounded_reconstructor_noise_error_le
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_noisy_reconstruction_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.localCFC_noisy_reconstruction_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_noisy_reconstruction_bound

end GegenbauerFock.GeneralUltrasphericalFock
