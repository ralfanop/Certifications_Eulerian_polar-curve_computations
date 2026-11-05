import GegenbauerFock.GegenbauerIntrinsicEntireTwoGramFullSpectrum
import GegenbauerFock.GegenbauerIntrinsicEntireGramSharpSpectrum
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramEssentialSingleton

/-!
# V007 — exact sharp spectral enclosure on the real holomorphic Fock output

The independently certified original ultraspherical source Gram has
full spectrum contained in the sharp closed nonnegative real interval
[0, ||C||²]. The full ordinary spectra of the genuine source Gram
and the true holomorphic Gaussian output Gram have been proven equal
by the original ultraspherical-to-entire-Gaussian Hilbert analysis
operator (not an identification of their distinct Hilbert spaces).

This module transfers that exact spectral localization to the actual
complete entire Gaussian L² output, and combines it with the already
kernel-checked full Fredholm essential singleton {0}. The result is
strictly stronger than positive-real localization alone.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every spectral point of the ACTUAL entire Gaussian L² holomorphic
output Gram is real nonnegative and bounded above by the exact
squared operator norm of the ultraspherical coefficient transform. -/
theorem C_intrinsicEntire_outputGram_spectral_value_sharp_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
      (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha) →
       (mu.re : ℂ) = mu ∧
       0 ≤ mu.re ∧
       mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  intro hmu
  have heq := C_intrinsicEntire_two_gram_full_spectrum_eq
    lam alpha hlam ha
  have hsource :
      mu ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) := by
    rw [heq]
    exact hmu
  exact intrinsicEntire_sourceGram_spectral_value_sharp_bound
    lam alpha hlam ha mu hsource

/-- Complete sharp spectral band and exact essential singleton for
the genuine analytic Gaussian output Gram, not a coefficient cutoff. -/
theorem C_intrinsicEntire_outputGram_sharp_spectrum_and_essential_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
      (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     (∀ mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha),
       (mu.re : ℂ) = mu ∧
       0 ≤ mu.re ∧
       mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖) ∧
     fredholmEssentialSpectrum
       (C_intrinsicEntire_outputGram lam alpha hlam ha) =
       ({0} : Set ℂ)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact ⟨C_intrinsicEntire_outputGram_spectral_value_sharp_bound
      lam alpha hlam ha,
    C_intrinsicEntire_outputGram_fredholm_essential_eq_singleton_zero
      lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_spectral_value_sharp_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_sharp_spectrum_and_essential_zero

end GegenbauerFock.GeneralUltrasphericalFock
