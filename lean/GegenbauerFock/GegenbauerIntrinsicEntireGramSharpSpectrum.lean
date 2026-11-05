import GegenbauerFock.GegenbauerIntrinsicEntireGramEssentialSingleton
import GegenbauerFock.TwoSidedGramExactSpectralNormBand

/-!
# V007 — exact spectral enclosure in the genuine intrinsic entire Gaussian Fock source

The original ultraspherical-to-entire-Fock map C_hol, with its
independently closed entire Gaussian L² codomain, defines a genuine
source Gram G_hol = C_hol† C_hol. The certified Hilbert isometry to the
coefficient Fock space proves G_hol = C†C without claiming that C_hol
itself is surjective.

Consequently the complete complex spectrum of G_hol lies in the
exact closed interval [0, ‖C‖²], and every parameter outside that
interval lies in its scalar resolvent. Separately the *Fredholm*
essential spectrum of the same actual operator equals {0}.

All conclusions concern full Hilbert-space operators, not finite
cutoffs or a merely formal polynomial span.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every spectral value of the genuine ultraspherical Gram formed
using the intrinsic entire Gaussian Bargmann–Fock Hilbert space
is nonnegative real and at most the exact squared coefficient
analysis norm. -/
theorem intrinsicEntire_sourceGram_spectral_value_sharp_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hm : mu ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧
      0 ≤ mu.re ∧
      mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha] at hm
  exact sourceGram_spectrum_bounded_by_analysis_norm_sq lam alpha hlam ha mu hm

/-- The genuine intrinsic entire-Gaussian source Gram is invertible
after every complex spectral shift outside the full exact interval. -/
theorem intrinsicEntire_sourceGram_outside_sharp_band_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (h : mu.im ≠ 0 ∨ mu.re < 0 ∨
      ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ < mu.re) :
    mu ∈ resolventSet ℂ (C_intrinsicEntire_gram lam alpha hlam ha) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact (two_sided_gram_outside_norm_sq_interval_resolvent
    lam alpha hlam ha mu h).1

/-- Sharp spectral localization and complete Fredholm-essential
classification for the true holomorphic Gaussian source Gram,
combined in a single certified operator theorem. -/
theorem intrinsicEntire_sourceGram_sharp_spectrum_and_essential_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (∀ mu ∈ spectrum ℂ (C_intrinsicEntire_gram lam alpha hlam ha),
       (mu.re : ℂ) = mu ∧
       0 ≤ mu.re ∧
       mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖) ∧
    fredholmEssentialSpectrum (C_intrinsicEntire_gram lam alpha hlam ha) =
      ({0} : Set ℂ) := by
  exact ⟨intrinsicEntire_sourceGram_spectral_value_sharp_bound lam alpha hlam ha,
    intrinsicEntire_sourceGram_fredholm_essential_eq_zero lam alpha hlam ha⟩

/-- Exact Fredholm classification for spectral shifts of the
genuine entire-Gaussian Fock source Gram: the shift is Fredholm
precisely when its complex spectral parameter is not zero. -/
theorem intrinsicEntire_sourceGram_shift_fredholm_iff_nonzero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) :
    ContinuousLinearMap.IsFredholm
      (C_intrinsicEntire_gram lam alpha hlam ha -
        mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
          Lp ℂ 2 (Ultraspherical.measure lam))) ↔ mu ≠ 0 := by
  have hess :
      mu ∈ fredholmEssentialSpectrum
          (C_intrinsicEntire_gram lam alpha hlam ha) ↔ mu = 0 := by
    rw [intrinsicEntire_sourceGram_fredholm_essential_eq_zero lam alpha hlam ha]
    simp only [Set.mem_singleton_iff]
  change (¬ ContinuousLinearMap.IsFredholm
    (C_intrinsicEntire_gram lam alpha hlam ha -
      mu • (1 : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)))) ↔ mu = 0 at hess
  tauto

#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_sourceGram_spectral_value_sharp_bound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_sourceGram_outside_sharp_band_resolvent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_sourceGram_sharp_spectrum_and_essential_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_sourceGram_shift_fredholm_iff_nonzero

end GegenbauerFock.GeneralUltrasphericalFock
