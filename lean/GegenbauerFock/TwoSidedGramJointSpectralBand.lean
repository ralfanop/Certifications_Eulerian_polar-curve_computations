import GegenbauerFock.TwoSidedGramNegativeResolvent
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# V007 — explicit joint spectral enclosure for both true Grams

The compact positive Grams act on different Hilbert spaces but have the
same full spectrum. Combining positivity, spectral equality, and the
norm bound on the spectrum gives a single quantitative enclosure by
the *smaller* of the two operator norms.

This is not an equality of operator norms or an eigenvalue computation.
In particular it uses neither a finite matrix truncation nor any
assumption that the Gegenbauer–Fock transform is onto.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every spectral point shared by the two actual Grams is real and
lies between zero and the minimum of their respective operator norms. -/
theorem two_sided_gram_joint_spectral_band
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hm : mu ∈ spectrum ℂ (gram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧
      0 ≤ mu.re ∧
      mu.re ≤ min ‖gram lam alpha hlam ha‖
        ‖outputGram lam alpha hlam ha‖ := by
  obtain ⟨hreal, hpos⟩ :=
    (two_sided_gram_spectra_nonnegative_real lam alpha hlam ha).1 mu hm
  have hmout : mu ∈ spectrum ℂ (outputGram lam alpha hlam ha) :=
    (two_sided_gram_spectrum_eq lam alpha hlam ha) ▸ hm
  have hsrcnorm : ‖mu‖ ≤ ‖gram lam alpha hlam ha‖ :=
    spectrum.norm_le_norm_of_mem hm
  have houtnorm : ‖mu‖ ≤ ‖outputGram lam alpha hlam ha‖ :=
    spectrum.norm_le_norm_of_mem hmout
  refine ⟨hreal, hpos, le_min ?_ ?_⟩
  · exact (Complex.re_le_norm mu).trans hsrcnorm
  · exact (Complex.re_le_norm mu).trans houtnorm

/-- Positive real spectral parameters above both actual spectral
radiuses are in the common resolvent. The bound uses the minimum of
operator norms because the two full spectra are equal. -/
theorem two_sided_gram_right_halfplane_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmu : min ‖gram lam alpha hlam ha‖
        ‖outputGram lam alpha hlam ha‖ < mu.re) :
    mu ∈ resolventSet ℂ (gram lam alpha hlam ha) ∧
      mu ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
  have hnot : mu ∉ spectrum ℂ (gram lam alpha hlam ha) := by
    intro hm
    exact (not_le_of_gt hmu)
      (two_sided_gram_joint_spectral_band lam alpha hlam ha mu hm).2.2
  have hres : mu ∈ resolventSet ℂ (gram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  exact ⟨hres,
    (two_sided_gram_resolventSet_eq lam alpha hlam ha) ▸ hres⟩

/-- All complex parameters with negative real part belong to the
common resolvent. Unlike the preceding real-axis regularization,
this excludes an entire open complex half-plane from each spectrum. -/
theorem two_sided_gram_left_halfplane_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu.re < 0) :
    mu ∈ resolventSet ℂ (gram lam alpha hlam ha) ∧
      mu ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
  have hnot : mu ∉ spectrum ℂ (gram lam alpha hlam ha) := by
    intro hm
    exact (not_le_of_gt hmu)
      ((two_sided_gram_spectra_nonnegative_real lam alpha hlam ha).1 mu hm).2
  have hres : mu ∈ resolventSet ℂ (gram lam alpha hlam ha) := by
    simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot
  exact ⟨hres,
    (two_sided_gram_resolventSet_eq lam alpha hlam ha) ▸ hres⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_joint_spectral_band
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_right_halfplane_resolvent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_left_halfplane_resolvent

end GegenbauerFock.GeneralUltrasphericalFock
