import GegenbauerFock.GegenbauerIntrinsicEntireTwoGramFullSpectrum
import GegenbauerFock.TwoSidedGramExactSpectralNormBand

/-!
# V007 — exact resolvent equality of the two true entire-Gaussian Grams

The full ordinary spectra of the two distinct actual Hilbert-space
Grams are separately certified equal, including zero. Since each
operator's resolvent is the complement of its full ordinary spectrum,
the sets of all resolvent parameters are also identical.

Independently, the source Gram is known to have every parameter
outside [0, ‖C‖²] in its resolvent, by genuine ultraspherical
operator analysis. We transfer that spectral exclusion to the
actual complete holomorphic Gaussian L² Bargmann–Fock output Gram.
Neither assertion identifies the Hilbert spaces or uses truncations.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Source and actual analytic Gaussian output Grams have identical
full scalar resolvent sets despite acting on distinct Hilbert spaces. -/
theorem C_intrinsicEntire_two_gram_resolventSet_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     resolventSet ℂ (C_intrinsicEntire_gram lam alpha hlam ha) =
       resolventSet ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hs := C_intrinsicEntire_two_gram_full_spectrum_eq lam alpha hlam ha
  ext mu
  have hmu :
      mu ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha) ↔
        mu ∈ spectrum ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha) :=
    Set.ext_iff.mp hs mu
  simpa only [spectrum, Set.mem_compl_iff, not_not] using not_congr hmu

/-- All complex parameters outside the exact squared-analysis-norm
spectral interval lie in the resolvent of the genuine entire
Gaussian Bargmann–Fock holomorphic output Gram. -/
theorem C_intrinsicEntire_outputGram_outside_sharp_band_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (h : mu.im ≠ 0 ∨ mu.re < 0 ∨
      ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ < mu.re) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     mu ∈ resolventSet ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hs : mu ∈ resolventSet ℂ
      (C_intrinsicEntire_gram lam alpha hlam ha) := by
    rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
    exact (two_sided_gram_outside_norm_sq_interval_resolvent
      lam alpha hlam ha mu h).1
  exact (Set.ext_iff.mp
      (C_intrinsicEntire_two_gram_resolventSet_eq lam alpha hlam ha) mu).mp hs

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_resolventSet_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_outside_sharp_band_resolvent

end GegenbauerFock.GeneralUltrasphericalFock
