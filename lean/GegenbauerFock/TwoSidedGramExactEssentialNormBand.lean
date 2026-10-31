import GegenbauerFock.TwoSidedGramEssentialSpectralBand
import GegenbauerFock.TwoSidedGramExactOperatorNorm

/-!
# V007 — sharp common Fredholm-essential spectral norm enclosure

For the two actual compact ultraspherical Gegenbauer–Fock Grams,
their Fredholm essential spectra are each subsets of the nonnegative
real interval ending at the *exact* squared operator norm of the
underlying analysis map C. Zero belongs to both sets.

The construction leaves the distinct source/output Hilbert spaces
unchanged; it does not assert the still stronger singleton essential
spectrum theorem, which needs Fredholmness of all nonzero shifts.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Fredholm-essential values of the actual source Gram are real,
nonnegative and at most the exact squared analysis operator norm. -/
theorem sourceGram_essential_spectral_value_le_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hm : mu ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧ 0 ≤ mu.re ∧
      mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  simpa only [sourceGram_norm_eq_analysis_norm_sq,
    outputGram_norm_eq_analysis_norm_sq, min_self] using
      sourceGram_essential_spectral_value_in_joint_band lam alpha hlam ha mu hm

/-- The output Gram has the identical essential spectral bound,
without identifying its coefficient Hilbert space with source L². -/
theorem outputGram_essential_spectral_value_le_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hm : mu ∈ fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧ 0 ≤ mu.re ∧
      mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  simpa only [sourceGram_norm_eq_analysis_norm_sq,
    outputGram_norm_eq_analysis_norm_sq, min_self] using
      outputGram_essential_spectral_value_in_joint_band lam alpha hlam ha mu hm

/-- Both Fredholm essential spectra contain zero and lie in the
same explicit squared-analysis-norm spectral interval. -/
theorem two_sided_gram_essential_zero_with_exact_norm_band
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((0 : ℂ) ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha) ∩
      fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) ∧
    (∀ mu ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha),
      (mu.re : ℂ) = mu ∧ 0 ≤ mu.re ∧
        mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖) ∧
    (∀ mu ∈ fredholmEssentialSpectrum (outputGram lam alpha hlam ha),
      (mu.re : ℂ) = mu ∧ 0 ≤ mu.re ∧
        mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖) :=
  ⟨two_sided_gram_zero_mem_fredholm_essential_spectra lam alpha hlam ha,
    sourceGram_essential_spectral_value_le_analysis_norm_sq lam alpha hlam ha,
    outputGram_essential_spectral_value_le_analysis_norm_sq lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_essential_spectral_value_le_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_essential_spectral_value_le_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_essential_zero_with_exact_norm_band

end GegenbauerFock.GeneralUltrasphericalFock
