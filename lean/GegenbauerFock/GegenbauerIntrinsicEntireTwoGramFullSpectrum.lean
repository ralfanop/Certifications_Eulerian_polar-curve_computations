import GegenbauerFock.GegenbauerIntrinsicEntireNonzeroSingularTransfer
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramContinuousSpectrum
import GegenbauerFock.TwoSidedGramSpectrumEquality
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative

/-!
# V007 — full ordinary spectrum equality for the genuine intrinsic Fock Grams

The two Grams belong to different Hilbert spaces: the ultraspherical
L² source and the complete entire Gaussian L² holomorphic output.
They have identical nonzero point spectra by the previously verified
singular-vector transfer. Compactness and the Fredholm alternative
upgrade this to identical nonzero ordinary spectra. Zero is in the
continuous spectrum of both by independently audited Hilbert-space
constructions. Therefore their full ordinary spectra coincide.

In particular, this does NOT identify the two distinct Hilbert spaces
or assert surjectivity of the compact Gegenbauer analysis map.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Point eigenvalues of the coefficient Gram and the actual entire
Gaussian L² output Gram agree, with vectors transported by the
certified full Bargmann–Fock unitary. -/
theorem outputGram_hasEigenvalue_iff_intrinsicEntire
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) :
    HasEigenvalue (outputGram lam alpha hlam ha).toLinearMap mu ↔
    HasEigenvalue (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu := by
  constructor
  · intro h
    obtain ⟨Fc, hf⟩ := h.exists_hasEigenvector
    have hne : Fc ≠ 0 := (hasEigenvector_iff.mp hf).2
    have heq : outputGram lam alpha hlam ha Fc = mu • Fc :=
      mem_eigenspace_iff.mp (hasEigenvector_iff.mp hf).1
    obtain ⟨F, hFne, hFeq⟩ :=
      (outputGram_eigenvalue_iff_intrinsicEntire_outputGram
        lam alpha hlam ha mu).mp ⟨Fc, hne, heq⟩
    apply hasEigenvalue_of_hasEigenvector
    exact hasEigenvector_iff.mpr
      ⟨mem_eigenspace_iff.mpr hFeq, hFne⟩
  · intro h
    obtain ⟨F, hF⟩ := h.exists_hasEigenvector
    have hFne : F ≠ 0 := (hasEigenvector_iff.mp hF).2
    have hFeq : C_intrinsicEntire_outputGram lam alpha hlam ha F = mu • F :=
      mem_eigenspace_iff.mp (hasEigenvector_iff.mp hF).1
    obtain ⟨Fc, hfne, hfeq⟩ :=
      (outputGram_eigenvalue_iff_intrinsicEntire_outputGram
        lam alpha hlam ha mu).mpr ⟨F, hFne, hFeq⟩
    apply hasEigenvalue_of_hasEigenvector
    exact hasEigenvector_iff.mpr
      ⟨mem_eigenspace_iff.mpr hfeq, hfne⟩

/-- For each nonzero complex parameter, coefficient-side and TRUE
holomorphic Gaussian output operator spectral membership agree. -/
theorem outputGram_nonzero_spectrum_iff_intrinsicEntire
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     mu ∈ spectrum ℂ (outputGram lam alpha hlam ha) ↔
     mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hcoeff :=
    (outputGram_compact lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum hmu
  have hhol :=
    (C_intrinsicEntire_outputGram_compact lam alpha hlam ha).hasEigenvalue_iff_mem_spectrum hmu
  exact hcoeff.symm.trans
    ((outputGram_hasEigenvalue_iff_intrinsicEntire lam alpha hlam ha mu).trans hhol)

/-- Full equality of ordinary operator spectra for the actual
ultraspherical source Gram and the complete analytic output Fock Gram,
including the continuous spectral value zero. -/
theorem C_intrinsicEntire_two_gram_full_spectrum_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) =
       spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  ext mu
  by_cases hmu : mu = 0
  · subst mu
    exact ⟨fun _ => C_intrinsicEntire_outputGram_zero_mem_spectrum
        lam alpha hlam ha,
      fun _ => gram_zero_mem_spectrum lam alpha hlam ha⟩
  · exact (two_sided_gram_nonzero_spectrum_iff
      lam alpha hlam ha mu hmu).trans
      (outputGram_nonzero_spectrum_iff_intrinsicEntire
        lam alpha hlam ha mu hmu)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_hasEigenvalue_iff_intrinsicEntire
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_spectrum_iff_intrinsicEntire
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_full_spectrum_eq

end GegenbauerFock.GeneralUltrasphericalFock
