import GegenbauerFock.GegenbauerIntrinsicEntireGramEssentialSingleton
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramEssentialSingleton

/-!
# V007 — equal Fredholm essential spectra of both genuine intrinsic Grams

The independently certified source Gram is the actual ultraspherical
Hilbert operator C_hol† C_hol. The output Gram is the actual compact
operator C_hol C_hol† on the separately defined complete holomorphic
Gaussian L² Bargmann–Fock space. Neither Hilbert space is identified
with the other, nor is the compact analysis transform claimed onto.

Existing Lean-certified theorems separately establish that the entire
Fredholm essential spectrum of each genuine Gram is exactly {0}.
The present module packages that fact into a common two-sided statement
and an equality of their Fredholm essential spectral sets.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The two genuine Gram operators, on distinct ultraspherical-source
and intrinsic entire Gaussian output Hilbert spaces, both have
Fredholm essential spectrum exactly the singleton zero. -/
theorem C_intrinsicEntire_two_gram_fredholm_essential_singletons
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     fredholmEssentialSpectrum
       (C_intrinsicEntire_gram lam alpha hlam ha) = ({0} : Set ℂ) ∧
     fredholmEssentialSpectrum
       (C_intrinsicEntire_outputGram lam alpha hlam ha) = ({0} : Set ℂ)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact ⟨intrinsicEntire_sourceGram_fredholm_essential_eq_zero
      lam alpha hlam ha,
    C_intrinsicEntire_outputGram_fredholm_essential_eq_singleton_zero
      lam alpha hlam ha⟩

/-- The genuine source/output Gram operators have exactly the same
Fredholm essential spectral set, despite acting on different spaces. -/
theorem C_intrinsicEntire_two_gram_fredholm_essential_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     fredholmEssentialSpectrum
       (C_intrinsicEntire_gram lam alpha hlam ha) =
     fredholmEssentialSpectrum
       (C_intrinsicEntire_outputGram lam alpha hlam ha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  obtain ⟨hsource, houtput⟩ :=
    C_intrinsicEntire_two_gram_fredholm_essential_singletons
      lam alpha hlam ha
  exact hsource.trans houtput.symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_fredholm_essential_singletons
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_fredholm_essential_eq

end GegenbauerFock.GeneralUltrasphericalFock
