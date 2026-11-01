import GegenbauerFock.FredholmEssentialSpectrumResolventExclusion
import GegenbauerFock.TwoSidedGramPositiveSpectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# V007 — common explicit enclosure for the bilateral Fredholm essential spectra

The genuine source Gram C†C and output Gram CC† act on different
Hilbert spaces, but have the same operator spectrum. Each Fredholm
essential spectrum is a subset of its corresponding operator spectrum.

The already certified positive-real spectral localization and the
common spectral norm bound therefore enclose BOTH essential spectra
in the same explicit interval [0, min(‖C†C‖, ‖CC†‖)].

This is a nontrivial quantitative restriction on the possible
essential spectral parameters, but it is NOT a proof of the stronger
singleton equality {0}: elimination of nonzero Fredholm-essential
eigenvalues still requires a separate compact Fredholm argument.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Generic operator spectral bound, valid even if the Hilbert space
is zero. Continuous endomorphisms only have ‖1‖ ≤ 1, not the
NormOneClass equality required by spectrum.norm_le_norm_of_mem. -/
private theorem essentialBand_spectral_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (mu : ℂ) (h : mu ∈ spectrum ℂ T) :
    ‖mu‖ ≤ ‖T‖ := by
  have hid : ‖(1 : E →L[ℂ] E)‖ ≤ 1 := by
    change ‖ContinuousLinearMap.id ℂ E‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  calc
    ‖mu‖ ≤ ‖T‖ * ‖(1 : E →L[ℂ] E)‖ :=
      spectrum.norm_le_norm_mul_of_mem h
    _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left hid (norm_nonneg T)
    _ = ‖T‖ := mul_one _

/-- Every Fredholm-essential point of the genuine source Gram is real
and lies in the common explicit band determined by both operator norms. -/
theorem sourceGram_essential_spectral_value_in_joint_band
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmem : mu ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧
      0 ≤ mu.re ∧
      mu.re ≤ min ‖gram lam alpha hlam ha‖
        ‖outputGram lam alpha hlam ha‖ := by
  have hspec : mu ∈ spectrum ℂ (gram lam alpha hlam ha) :=
    fredholmEssentialSpectrum_subset_spectrum
      (gram lam alpha hlam ha) hmem
  obtain ⟨hreal, hpos⟩ :=
    (two_sided_gram_spectra_nonnegative_real lam alpha hlam ha).1 mu hspec
  have hout : mu ∈ spectrum ℂ (outputGram lam alpha hlam ha) :=
    (two_sided_gram_spectrum_eq lam alpha hlam ha) ▸ hspec
  have hsrcnorm : ‖mu‖ ≤ ‖gram lam alpha hlam ha‖ :=
    essentialBand_spectral_norm_le (gram lam alpha hlam ha) mu hspec
  have houtnorm : ‖mu‖ ≤ ‖outputGram lam alpha hlam ha‖ :=
    essentialBand_spectral_norm_le (outputGram lam alpha hlam ha) mu hout
  exact ⟨hreal, hpos,
    le_min ((Complex.re_le_norm mu).trans hsrcnorm)
      ((Complex.re_le_norm mu).trans houtnorm)⟩

/-- Every Fredholm-essential point of the genuine output Gram is also
real and in the SAME interval even though its Hilbert space differs. -/
theorem outputGram_essential_spectral_value_in_joint_band
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmem : mu ∈ fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧
      0 ≤ mu.re ∧
      mu.re ≤ min ‖gram lam alpha hlam ha‖
        ‖outputGram lam alpha hlam ha‖ := by
  have hout : mu ∈ spectrum ℂ (outputGram lam alpha hlam ha) :=
    fredholmEssentialSpectrum_subset_spectrum
      (outputGram lam alpha hlam ha) hmem
  have hsrc : mu ∈ spectrum ℂ (gram lam alpha hlam ha) :=
    (two_sided_gram_spectrum_eq lam alpha hlam ha).symm ▸ hout
  obtain ⟨hreal, hpos⟩ :=
    (two_sided_gram_spectra_nonnegative_real lam alpha hlam ha).1 mu hsrc
  have hsrcnorm : ‖mu‖ ≤ ‖gram lam alpha hlam ha‖ :=
    essentialBand_spectral_norm_le (gram lam alpha hlam ha) mu hsrc
  have houtnorm : ‖mu‖ ≤ ‖outputGram lam alpha hlam ha‖ :=
    essentialBand_spectral_norm_le (outputGram lam alpha hlam ha) mu hout
  exact ⟨hreal, hpos,
    le_min ((Complex.re_le_norm mu).trans hsrcnorm)
      ((Complex.re_le_norm mu).trans houtnorm)⟩

/-- Both separate Fredholm essential spectra are contained in the
same nonnegative real compact spectral band. -/
theorem two_sided_gram_essential_spectra_in_joint_band
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∀ mu ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha),
      (mu.re : ℂ) = mu ∧
        0 ≤ mu.re ∧
        mu.re ≤ min ‖gram lam alpha hlam ha‖
          ‖outputGram lam alpha hlam ha‖) ∧
    (∀ mu ∈ fredholmEssentialSpectrum (outputGram lam alpha hlam ha),
      (mu.re : ℂ) = mu ∧
        0 ≤ mu.re ∧
        mu.re ≤ min ‖gram lam alpha hlam ha‖
          ‖outputGram lam alpha hlam ha‖) :=
  ⟨sourceGram_essential_spectral_value_in_joint_band lam alpha hlam ha,
   outputGram_essential_spectral_value_in_joint_band lam alpha hlam ha⟩

/-- Zero belongs to both Fredholm essential spectra and both spectra
obey the common explicitly bounded nonnegative real localization. -/
theorem two_sided_gram_essential_zero_and_joint_band
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((0 : ℂ) ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha) ∩
      fredholmEssentialSpectrum (outputGram lam alpha hlam ha)) ∧
    (∀ mu ∈ fredholmEssentialSpectrum (gram lam alpha hlam ha),
      (mu.re : ℂ) = mu ∧
        0 ≤ mu.re ∧
        mu.re ≤ min ‖gram lam alpha hlam ha‖
          ‖outputGram lam alpha hlam ha‖) ∧
    (∀ mu ∈ fredholmEssentialSpectrum (outputGram lam alpha hlam ha),
      (mu.re : ℂ) = mu ∧
        0 ≤ mu.re ∧
        mu.re ≤ min ‖gram lam alpha hlam ha‖
          ‖outputGram lam alpha hlam ha‖) := by
  exact ⟨two_sided_gram_zero_mem_fredholm_essential_spectra lam alpha hlam ha,
    (two_sided_gram_essential_spectra_in_joint_band lam alpha hlam ha).1,
    (two_sided_gram_essential_spectra_in_joint_band lam alpha hlam ha).2⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_essential_spectral_value_in_joint_band
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_essential_spectral_value_in_joint_band
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_essential_spectra_in_joint_band
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_essential_zero_and_joint_band

end GegenbauerFock.GeneralUltrasphericalFock
