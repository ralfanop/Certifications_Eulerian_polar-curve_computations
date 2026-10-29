import GegenbauerFock.FredholmEssentialSpectrumResolventExclusion
import GegenbauerFock.TwoSidedGramJointSpectralBand

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
  exact two_sided_gram_joint_spectral_band lam alpha hlam ha mu hspec

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
  exact two_sided_gram_joint_spectral_band lam alpha hlam ha mu hsrc

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
