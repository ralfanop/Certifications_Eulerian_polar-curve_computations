import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramSpectral
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramContinuousSpectrum
import GegenbauerFock.GegenbauerIntrinsicEntireTwoGramFullSpectrum
import GegenbauerFock.TwoSidedGramPositiveSpectrum

/-!
# V007 — actual holomorphic Gaussian output Gram spectrum is nonnegative real

The genuine entire Gaussian L² output Gram H_hol is compact,
self-adjoint and positive by the exact-source checked theorem group.
Every nonzero spectral parameter is an actual eigenvalue by the
Fredholm alternative, and hence must be a strictly positive real
number. Zero is already known to lie in continuous spectrum.

These statements characterize the location of ALL spectral values
without identifying the ultraspherical source Hilbert space with
the holomorphic Gaussian output Hilbert space, or using finite
truncations of the operator.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every nonzero complex spectral value of the actual holomorphic
Gaussian L² output Gram is a strictly positive real value. -/
theorem C_intrinsicEntire_outputGram_nonzero_spectral_value_positive_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0)
    :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha) →
       (mu.re : ℂ) = mu ∧ 0 < mu.re) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  intro hmem
  have heq := C_intrinsicEntire_two_gram_full_spectrum_eq
    lam alpha hlam ha
  have hsource :
      mu ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) := by
    rw [heq]
    exact hmem
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha] at hsource
  exact source_gram_nonzero_spectral_value_positive_real
    lam alpha hlam ha mu hmu hsource

/-- Every spectral value of the ACTUAL holomorphic Gaussian Fock
output Gram belongs to the nonnegative real axis of ℂ. -/
theorem C_intrinsicEntire_outputGram_spectrum_nonnegative_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     ∀ mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha),
       (mu.re : ℂ) = mu ∧ 0 ≤ mu.re) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  intro mu hmem
  by_cases hz : mu = 0
  · subst mu
    simp
  · obtain ⟨hr, hp⟩ :=
      C_intrinsicEntire_outputGram_nonzero_spectral_value_positive_real
        lam alpha hlam ha mu hz hmem
    exact ⟨hr, hp.le⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_nonzero_spectral_value_positive_real
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_spectrum_nonnegative_real

end GegenbauerFock.GeneralUltrasphericalFock
