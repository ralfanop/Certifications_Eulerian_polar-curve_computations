import GegenbauerFock.TwoSidedGramEssentialSpectrumSingleton

/-!
# V007 — translation covariance of the Fredholm essential spectrum

For the Fredholm definition of essential spectrum, translating an
operator by a complex scalar translates its Fredholm essential spectrum
by the same scalar. Applied to the concrete ultraspherical and Gaussian
Fock Grams, the translated essential spectra are exactly singletons.

This is an operator-level statement about the two full Hilbert spaces.
It neither replaces either Gram by finite truncations nor identifies
the distinct Hilbert spaces. Axiom auditing is supplied separately.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Adding a scalar multiple of the identity translates every Fredholm
essential spectral parameter, with no compactness assumption. -/
theorem fredholmEssentialSpectrum_scalar_add_iff
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (c mu : ℂ) :
    mu ∈ fredholmEssentialSpectrum
      (T + c • (1 : H →L[ℂ] H)) ↔
    mu - c ∈ fredholmEssentialSpectrum T := by
  have hshift :
      (T + c • (1 : H →L[ℂ] H)) - mu • (1 : H →L[ℂ] H) =
      T - (mu - c) • (1 : H →L[ℂ] H) := by
    rw [sub_smul]
    abel
  simp only [fredholmEssentialSpectrum, Set.mem_setOf_eq, hshift]

/-- For each positive ultraspherical/Gaussian parameter pair, the source
Gram plus an arbitrary complex scalar has Fredholm essential spectrum
exactly that scalar. -/
theorem sourceGram_translated_fredholm_essential_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℂ) :
    fredholmEssentialSpectrum
      (gram lam alpha hlam ha +
        c • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) =
      ({c} : Set ℂ) := by
  ext mu
  rw [fredholmEssentialSpectrum_scalar_add_iff,
    sourceGram_fredholm_essential_spectrum_eq_singleton_zero lam alpha hlam ha]
  simp only [Set.mem_singleton_iff, sub_eq_zero]

/-- The same exact scalar-translation identity holds for the genuine
full Gaussian-Fock coefficient output Gram. -/
theorem outputGram_translated_fredholm_essential_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℂ) :
    fredholmEssentialSpectrum
      (outputGram lam alpha hlam ha +
        c • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) =
      ({c} : Set ℂ) := by
  ext mu
  rw [fredholmEssentialSpectrum_scalar_add_iff,
    outputGram_fredholm_essential_spectrum_eq_singleton_zero lam alpha hlam ha]
  simp only [Set.mem_singleton_iff, sub_eq_zero]

/-- The two scalar-shifted concrete Gram essential spectra coincide,
and their common value is the precise singleton containing the shift. -/
theorem two_sided_gram_translated_fredholm_essential_spectra
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (c : ℂ) :
    fredholmEssentialSpectrum
      (gram lam alpha hlam ha +
        c • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) =
      ({c} : Set ℂ) ∧
    fredholmEssentialSpectrum
      (outputGram lam alpha hlam ha +
        c • (1 : InfiniteAnalysis.FockCoefficients →L[ℂ]
          InfiniteAnalysis.FockCoefficients)) =
      ({c} : Set ℂ) :=
  ⟨sourceGram_translated_fredholm_essential_spectrum lam alpha hlam ha c,
    outputGram_translated_fredholm_essential_spectrum lam alpha hlam ha c⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fredholmEssentialSpectrum_scalar_add_iff
#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_translated_fredholm_essential_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_translated_fredholm_essential_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_translated_fredholm_essential_spectra

end GegenbauerFock.GeneralUltrasphericalFock
