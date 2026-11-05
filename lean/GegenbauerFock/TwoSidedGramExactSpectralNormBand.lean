import GegenbauerFock.TwoSidedGramJointSpectralBand
import GegenbauerFock.TwoSidedGramExactOperatorNorm
import GegenbauerFock.TwoSidedGramNonrealResolvent

/-!
# V007 — concrete spectral band in the squared Gegenbauer–Fock analysis norm

The genuine source and target Grams have exactly the same full complex
spectrum, both lie on the nonnegative real axis, and both have operator
norm precisely ‖C‖². The resulting common spectral enclosure has a
parameter-independent description in terms of the actual Gegenbauer–Fock
analysis map.

Every complex parameter outside the closed real segment [0, ‖C‖²]
belongs to both exact resolvent sets. These statements are valid for
the complete ultraspherical and coefficient Hilbert spaces separately.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every source spectral value lies in the positive interval determined
by the exact squared norm of the genuine analysis operator. -/
theorem sourceGram_spectrum_bounded_by_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hm : mu ∈ spectrum ℂ (gram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧
      0 ≤ mu.re ∧
      mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  simpa only [sourceGram_norm_eq_analysis_norm_sq,
    outputGram_norm_eq_analysis_norm_sq, min_self]
    using two_sided_gram_joint_spectral_band lam alpha hlam ha mu hm

/-- The exact same spectral bound holds on the true Fock coefficient
space, without identifying its Hilbert space with ultraspherical L². -/
theorem outputGram_spectrum_bounded_by_analysis_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hm : mu ∈ spectrum ℂ (outputGram lam alpha hlam ha)) :
    (mu.re : ℂ) = mu ∧
      0 ≤ mu.re ∧
      mu.re ≤ ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ := by
  have hs : mu ∈ spectrum ℂ (gram lam alpha hlam ha) :=
    (two_sided_gram_spectrum_eq lam alpha hlam ha).symm ▸ hm
  exact sourceGram_spectrum_bounded_by_analysis_norm_sq
    lam alpha hlam ha mu hs

/-- Every complex scalar outside [0, ‖C‖²] is in both genuine
resolvent sets: nonreal parameters, negative real parameters, and
parameters to the right of the exact squared norm. -/
theorem two_sided_gram_outside_norm_sq_interval_resolvent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (h : mu.im ≠ 0 ∨ mu.re < 0 ∨
      ‖C lam alpha hlam ha‖ * ‖C lam alpha hlam ha‖ < mu.re) :
    mu ∈ resolventSet ℂ (gram lam alpha hlam ha) ∧
      mu ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
  rcases h with him | hneg | hgt
  · exact two_sided_gram_nonreal_mem_resolventSet lam alpha hlam ha mu him
  · exact two_sided_gram_left_halfplane_resolvent lam alpha hlam ha mu hneg
  · apply two_sided_gram_right_halfplane_resolvent lam alpha hlam ha mu
    simpa only [sourceGram_norm_eq_analysis_norm_sq,
      outputGram_norm_eq_analysis_norm_sq, min_self] using hgt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_spectrum_bounded_by_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_spectrum_bounded_by_analysis_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_outside_norm_sq_interval_resolvent

end GegenbauerFock.GeneralUltrasphericalFock
