import GegenbauerFock.GegenbauerIntrinsicEntireTwoGramEssentialSpectra

/-!
# V007 — exact Fredholm shift criterion for the two genuine intrinsic Grams

The source Gram of the ultraspherical-to-entire Gaussian L² transform
and the true output Gram on the intrinsic holomorphic Bargmann–Fock
Hilbert space have both been independently certified to have Fredholm
essential spectrum exactly {0}. By the definition of Fredholm
essential spectrum, the shift of either genuine operator is Fredholm
precisely at nonzero complex spectral parameters.

The output space is the complete closed Gaussian L² holomorphic
subspace; this is not a coefficient-only or finite-section statement.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero complex shift of the true Gaussian Fock output Gram
is Fredholm, and its unshifted version is not Fredholm. -/
theorem C_intrinsicEntire_outputGram_shift_fredholm_iff_nonzero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (mu : ℂ) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     ContinuousLinearMap.IsFredholm
       (C_intrinsicEntire_outputGram lam alpha hlam ha -
         mu • (1 : GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
           GaussianArea.entireGaussianL2Submodule alpha)) ↔ mu ≠ 0) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hess :
      mu ∈ fredholmEssentialSpectrum
        (C_intrinsicEntire_outputGram lam alpha hlam ha) ↔ mu = 0 := by
    rw [C_intrinsicEntire_outputGram_fredholm_essential_eq_singleton_zero
      lam alpha hlam ha]
    simp only [Set.mem_singleton_iff]
  change (¬ ContinuousLinearMap.IsFredholm
    (C_intrinsicEntire_outputGram lam alpha hlam ha -
      mu • (1 : GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
        GaussianArea.entireGaussianL2Submodule alpha))) ↔ mu = 0 at hess
  tauto

/-- The source and true holomorphic output Gram shifts are
simultaneously Fredholm exactly for nonzero spectral parameters. -/
theorem C_intrinsicEntire_two_gram_shifts_fredholm_iff_nonzero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (mu : ℂ) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     (ContinuousLinearMap.IsFredholm
       (C_intrinsicEntire_gram lam alpha hlam ha -
         mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
           Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      ContinuousLinearMap.IsFredholm
       (C_intrinsicEntire_outputGram lam alpha hlam ha -
         mu • (1 : GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
           GaussianArea.entireGaussianL2Submodule alpha))) ↔ mu ≠ 0) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hs :
      (ContinuousLinearMap.IsFredholm
       (C_intrinsicEntire_gram lam alpha hlam ha -
         mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
           Lp ℂ 2 (Ultraspherical.measure lam)))) ↔ mu ≠ 0 := by
    have hmem :
        mu ∈ fredholmEssentialSpectrum
          (C_intrinsicEntire_gram lam alpha hlam ha) ↔ mu = 0 := by
      rw [intrinsicEntire_sourceGram_fredholm_essential_eq_zero
        lam alpha hlam ha]
      simp only [Set.mem_singleton_iff]
    change (¬ ContinuousLinearMap.IsFredholm
      (C_intrinsicEntire_gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam)))) ↔ mu = 0 at hmem
    tauto
  have ho := C_intrinsicEntire_outputGram_shift_fredholm_iff_nonzero
    lam alpha hlam ha mu
  constructor
  · exact fun h => hs.mp h.1
  · intro h
    exact ⟨hs.mpr h, ho.mpr h⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_shift_fredholm_iff_nonzero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_shifts_fredholm_iff_nonzero

end GegenbauerFock.GeneralUltrasphericalFock
