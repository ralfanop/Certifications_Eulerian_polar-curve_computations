import GegenbauerFock.TwoSidedGramNonzeroShiftFredholm

/-!
# V007 — both genuine Fredholm essential spectra are exactly {0}

The already audited zero non-Fredholm theorem provides membership of
zero in each essential spectrum. The separate nonzero-shift Fredholm
certificate excludes every μ≠0. These statements combine to show that
the essential spectrum of C†C on genuine ultraspherical L² and of CC†
on the full Fock coefficient Hilbert space both equal {0}.

This is NOT a statement about finite truncations, or an equality
between the underlying Hilbert spaces. CI must compile BOTH the
generic nonzero Fredholm bridge and these final consequences before
the singleton-spectrum results can be treated as certified.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The entire Fredholm essential spectrum of the genuine source
ultraspherical Gram is the singleton {0}. -/
theorem sourceGram_fredholm_essential_spectrum_eq_singleton_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    fredholmEssentialSpectrum (gram lam alpha hlam ha) =
      ({0} : Set ℂ) := by
  ext mu
  constructor
  · intro hmu
    by_contra hne
    have hmu_ne : mu ≠ 0 := by simpa using hne
    exact hmu (sourceGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu_ne)
  · intro hmu
    have hzero : mu = 0 := by simpa using hmu
    subst mu
    exact sourceGram_zero_mem_fredholm_essential_spectrum lam alpha hlam ha

/-- The entire Fredholm essential spectrum of the genuine output
Gaussian-Fock coefficient Gram is also {0}. -/
theorem outputGram_fredholm_essential_spectrum_eq_singleton_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    fredholmEssentialSpectrum (outputGram lam alpha hlam ha) =
      ({0} : Set ℂ) := by
  ext mu
  constructor
  · intro hmu
    by_contra hne
    have hmu_ne : mu ≠ 0 := by simpa using hne
    exact hmu (outputGram_nonzero_shift_isFredholm lam alpha hlam ha mu hmu_ne)
  · intro hmu
    have hzero : mu = 0 := by simpa using hmu
    subst mu
    exact outputGram_zero_mem_fredholm_essential_spectrum lam alpha hlam ha

/-- Identical singleton Fredholm essential spectra for the genuine
source and full output Grams on two distinct Hilbert spaces. -/
theorem two_sided_gram_fredholm_essential_spectra_singleton_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    fredholmEssentialSpectrum (gram lam alpha hlam ha) =
      ({0} : Set ℂ) ∧
    fredholmEssentialSpectrum (outputGram lam alpha hlam ha) =
      ({0} : Set ℂ) :=
  ⟨sourceGram_fredholm_essential_spectrum_eq_singleton_zero lam alpha hlam ha,
   outputGram_fredholm_essential_spectrum_eq_singleton_zero lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_fredholm_essential_spectrum_eq_singleton_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_fredholm_essential_spectrum_eq_singleton_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_fredholm_essential_spectra_singleton_zero

end GegenbauerFock.GeneralUltrasphericalFock
