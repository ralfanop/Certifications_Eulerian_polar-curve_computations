import GegenbauerFock.TwoSidedGramZeroSpectrum
import GegenbauerFock.TwoSidedSingularSpectralCompleteness

/-!
# V007 — zero is spectral but not an eigenvalue on either Hilbert side

The actual source and output Gram operators are compact, selfadjoint
and positive. Zero belongs to both operator spectra, but the genuine
zero eigenspaces both vanish. This combines the new zero-spectrum
obstructions with independently certified kernel-free singular
spectral completeness; the result does NOT identify the two Hilbert
spaces or claim that zero is a nonzero singular value.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem two_sided_gram_zero_spectral_not_eigen
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((0 : ℂ) ∈ spectrum ℂ (gram lam alpha hlam ha) ∧
      eigenspace (gram lam alpha hlam ha).toLinearMap (0 : ℂ) =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))) ∧
    ((0 : ℂ) ∈ spectrum ℂ (outputGram lam alpha hlam ha) ∧
      eigenspace (outputGram lam alpha hlam ha).toLinearMap (0 : ℂ) =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)) := by
  obtain ⟨hsrc, hout⟩ :=
    two_sided_zero_eigenspaces_bot lam alpha hlam ha
  have hsrc' :
      eigenspace (gram lam alpha hlam ha).toLinearMap (0 : ℂ) =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    rw [gram_eq_gramIntegralOperator lam alpha hlam ha]
    exact hsrc
  exact ⟨⟨gram_zero_mem_spectrum lam alpha hlam ha, hsrc'⟩,
    ⟨outputGram_zero_mem_spectrum lam alpha hlam ha, hout⟩⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_zero_spectral_not_eigen

end GegenbauerFock.GeneralUltrasphericalFock
