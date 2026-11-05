import GegenbauerFock.GegenbauerIntrinsicEntireGramIdentity
import GegenbauerFock.TwoSidedGramEssentialSpectrumSingleton
import GegenbauerFock.TwoSidedGramSpectrumEquality

/-!
# V007 — Fredholm essential singleton for the genuine intrinsic holomorphic source Gram

The separately built Gegenbauer analysis operator into the intrinsically
defined entire Gaussian L² Bargmann–Fock Hilbert space has a genuine
source Gram. The audited operator identity identifies that source Gram
with the original ultraspherical coefficient-side source Gram, without
identifying or replacing the different Hilbert codomains.

The common ordinary spectra follow from the already certified
two-sided Gram spectral equality. The stronger Fredholm essential
singletons are conditional *as certificates* on the independent
nonzero-shift Fredholm module passing the kernel CI and axiom audit.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine entire-Gaussian source Gram has exactly the full
ordinary spectrum of the actual Fock-coefficient output Gram. -/
theorem intrinsicEntire_sourceGram_spectrum_eq_coefficient_outputGram
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) =
      spectrum ℂ (outputGram lam alpha hlam ha) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact two_sided_gram_spectrum_eq lam alpha hlam ha

/-- The Fredholm essential spectrum of the genuine ultraspherical
source Gram with intrinsic holomorphic Gaussian codomain is {0}. -/
theorem intrinsicEntire_sourceGram_fredholm_essential_eq_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    fredholmEssentialSpectrum (C_intrinsicEntire_gram lam alpha hlam ha) =
      ({0} : Set ℂ) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact sourceGram_fredholm_essential_spectrum_eq_singleton_zero
    lam alpha hlam ha

/-- Both genuine realizations—source Gram formed in the intrinsic
entire Gaussian Fock codomain and output Gram on coefficient ℓ²—
have Fredholm essential spectrum exactly {0}. -/
theorem intrinsicEntire_source_and_coefficient_output_essential_singletons
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    fredholmEssentialSpectrum (C_intrinsicEntire_gram lam alpha hlam ha) =
        ({0} : Set ℂ) ∧
      fredholmEssentialSpectrum (outputGram lam alpha hlam ha) =
        ({0} : Set ℂ) := by
  exact ⟨intrinsicEntire_sourceGram_fredholm_essential_eq_zero
      lam alpha hlam ha,
    outputGram_fredholm_essential_spectrum_eq_singleton_zero
      lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_sourceGram_spectrum_eq_coefficient_outputGram
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_sourceGram_fredholm_essential_eq_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_source_and_coefficient_output_essential_singletons

end GegenbauerFock.GeneralUltrasphericalFock
