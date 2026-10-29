import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramContinuousSpectrum
import GegenbauerFock.GegenbauerIntrinsicEntireGramZeroSpectrum
import GegenbauerFock.TwoSidedGramFredholmEssentialSpectrum

/-!
# V007 — Fredholm essential zero of the real intrinsic Fock output Gram

The actual compact holomorphic-output Gram C_hol C_hol† acts on the
complete intrinsic Gaussian L² subspace of entire representatives.
Its image is proper dense and nonclosed. Since Mathlib Fredholm
operators must have closed range, this genuine output Hilbert map is
not Fredholm.

Consequently zero lies in the Fredholm essential spectrum of the
actual holomorphic Gaussian output Gram, not just the coefficient-side
model. The corresponding source result is already kernel-certified
through the Bochner Gram identity. No claim is made here about nonzero
Fredholm points or a full essential-spectral classification.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual analytic output Gram is not Fredholm: its image is
dense but not closed in the Gaussian holomorphic L² Hilbert space. -/
theorem C_intrinsicEntire_outputGram_zero_not_fredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ContinuousLinearMap.IsFredholm
      (C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  intro hfred
  exact (C_intrinsicEntire_outputGram_range_not_closed lam alpha hlam ha)
    hfred.isClosed_range

/-- The Fredholm essential spectrum of the actual intrinsic
Bargmann–Fock output Gram contains zero. -/
theorem C_intrinsicEntire_outputGram_zero_mem_fredholm_essential
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈
      fredholmEssentialSpectrum (C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  simpa [fredholmEssentialSpectrum] using
    C_intrinsicEntire_outputGram_zero_not_fredholm lam alpha hlam ha

/-- Simultaneous essential-spectral zero for the two genuine Gram
operators on their distinct ultraspherical and analytic Gaussian
Hilbert spaces. -/
theorem C_intrinsicEntire_two_gram_zero_fredholm_essential
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈
      fredholmEssentialSpectrum (C_intrinsicEntire_gram lam alpha hlam ha) ∧
    (0 : ℂ) ∈
      fredholmEssentialSpectrum (C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  exact ⟨C_intrinsicEntire_gram_zero_mem_fredholm_essential lam alpha hlam ha,
    C_intrinsicEntire_outputGram_zero_mem_fredholm_essential lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_zero_not_fredholm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_zero_mem_fredholm_essential
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_two_gram_zero_fredholm_essential

end GegenbauerFock.GeneralUltrasphericalFock
