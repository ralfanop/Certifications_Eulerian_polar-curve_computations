import GegenbauerFock.GegenbauerIntrinsicEntireGramIdentity
import GegenbauerFock.TwoSidedGramZeroNonEigen
import GegenbauerFock.TwoSidedGramFredholmEssentialSpectrum

/-!
# V007 — zero spectral boundary of the actual intrinsic Fock source Gram

The intrinsic holomorphic Gaussian Hilbert realization has exactly the
same bounded source Gram as the original Gegenbauer coefficient map.
It therefore inherits the subtle infinite-dimensional distinction:
zero belongs to the operator spectrum and to the Fredholm essential
spectrum, but is not an eigenvalue.

This theorem is about the *source Gram* on genuine ultraspherical L².
It does not assert a zero mode in the holomorphic Fock codomain and
does not confuse dense range with surjectivity.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Zero belongs to the actual operator spectrum of the intrinsic
holomorphic Gegenbauer–Fock source Gram. -/
theorem C_intrinsicEntire_gram_zero_mem_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact gram_zero_mem_spectrum lam alpha hlam ha

/-- Zero is not an eigenvalue: the genuine intrinsic source Gram has
trivial zero eigenspace, despite zero lying in its spectrum. -/
theorem C_intrinsicEntire_gram_zero_not_eigen
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap (0 : ℂ) =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact (two_sided_gram_zero_spectral_not_eigen lam alpha hlam ha).1.2

/-- Zero also lies in the genuine Fredholm essential spectrum of the
intrinsic holomorphic source Gram, hence no bounded inverse exists. -/
theorem C_intrinsicEntire_gram_zero_mem_fredholm_essential
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈
      fredholmEssentialSpectrum (C_intrinsicEntire_gram lam alpha hlam ha) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact sourceGram_zero_mem_fredholm_essential_spectrum lam alpha hlam ha

/-- Joint spectral/essential-spectral membership with no zero
eigenvectors for the genuine holomorphic source Gram. -/
theorem C_intrinsicEntire_gram_zero_continuous_essential
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) ∧
    (0 : ℂ) ∈ fredholmEssentialSpectrum
      (C_intrinsicEntire_gram lam alpha hlam ha) ∧
    eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap 0 =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  exact ⟨C_intrinsicEntire_gram_zero_mem_spectrum lam alpha hlam ha,
    C_intrinsicEntire_gram_zero_mem_fredholm_essential lam alpha hlam ha,
    C_intrinsicEntire_gram_zero_not_eigen lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_zero_mem_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_zero_not_eigen
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_zero_mem_fredholm_essential
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_zero_continuous_essential

end GegenbauerFock.GeneralUltrasphericalFock
