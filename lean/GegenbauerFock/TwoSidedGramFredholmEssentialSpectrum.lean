import GegenbauerFock.TwoSidedGramZeroNotFredholm
import GegenbauerFock.TwoSidedGramSingularWeylZero

/-!
# V007 — zero in the genuine Fredholm essential spectra of both Gram operators

For a bounded endomorphism T of a complex Hilbert space, its
Fredholm essential spectrum is the set of z such that T - z•I
is NOT Fredholm. This is the standard Fredholm convention (up to
the immaterial overall sign of z•I-T).

For the actual two Grams G=C†C and H=CC†, prior kernel-certified
results show their images are not closed and their zero point is not
an eigenvalue. The new no-Fredholm theorem yields the exact essential
spectral membership 0∈σ_ess(G)∩σ_ess(H).

The accompanying singular Weyl sequences are independently
kernel-certified. The two Hilbert spaces remain distinct and the
analysis map is not claimed surjective. We do NOT claim here that the
entire essential spectra equal {0}; that stronger claim is separate.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The Fredholm essential spectrum of a bounded endomorphism of a
complex Hilbert space, defined in the exact Mathlib IsFredholm sense. -/
def fredholmEssentialSpectrum
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) : Set ℂ :=
  {z | ¬ ContinuousLinearMap.IsFredholm (T - z • (1 : H →L[ℂ] H))}

/-- Zero is in the Fredholm essential spectrum of the genuine
ultraspherical source Gram, rather than merely in its point spectrum. -/
theorem sourceGram_zero_mem_fredholm_essential_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha) := by
  simpa [fredholmEssentialSpectrum] using
    sourceGram_zero_not_fredholm lam alpha hlam ha

/-- Zero is in the Fredholm essential spectrum of the genuine
Gaussian-Fock coefficient output Gram. -/
theorem outputGram_zero_mem_fredholm_essential_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ fredholmEssentialSpectrum (outputGram lam alpha hlam ha) := by
  simpa [fredholmEssentialSpectrum] using
    outputGram_zero_not_fredholm lam alpha hlam ha

/-- Bilateral essential-spectral membership of zero, on the two
different Hilbert spaces and using genuine bounded Grams. -/
theorem two_sided_gram_zero_mem_fredholm_essential_spectra
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈
      fredholmEssentialSpectrum (gram lam alpha hlam ha) ∩
      fredholmEssentialSpectrum (outputGram lam alpha hlam ha) :=
  ⟨sourceGram_zero_mem_fredholm_essential_spectrum lam alpha hlam ha,
    outputGram_zero_mem_fredholm_essential_spectrum lam alpha hlam ha⟩

/-- The essential spectral zero has singular Weyl witnesses on both
sides: this combines independently established Fredholm and sequence
certificates without identifying the underlying spaces. -/
theorem two_sided_gram_zero_essential_and_singular_weyl
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((0 : ℂ) ∈
      fredholmEssentialSpectrum (gram lam alpha hlam ha) ∩
      fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) ∧
    (∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      IsSingularWeylSequenceAtZero (gram lam alpha hlam ha) u) ∧
    (∃ v : ℕ → InfiniteAnalysis.FockCoefficients,
      IsSingularWeylSequenceAtZero (outputGram lam alpha hlam ha) v) := by
  exact ⟨two_sided_gram_zero_mem_fredholm_essential_spectra lam alpha hlam ha,
    sourceGram_has_singular_weyl_sequence_at_zero lam alpha hlam ha,
    outputGram_has_singular_weyl_sequence_at_zero lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_zero_mem_fredholm_essential_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_mem_fredholm_essential_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_zero_mem_fredholm_essential_spectra
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_zero_essential_and_singular_weyl

end GegenbauerFock.GeneralUltrasphericalFock
