import GegenbauerFock.TwoSidedGramPositiveSpectrum

/-!
# V007 — shared resolvent and negative-real regularization

The genuine source Gram C†C and full output Gram CC† have equal
complex spectra even though they act on different Hilbert spaces.
Therefore their resolvent sets agree as sets of scalar parameters.

Since both spectra consist of nonnegative real numbers, every
strictly negative real parameter belongs to both resolvent sets.
Equivalently, adding any strictly positive real scalar multiple
of the identity makes either Gram invertible. This is an exact
infinite-dimensional spectral statement, with no finite truncation.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Scalar resolvent domains coincide for the two actual Grams. -/
theorem two_sided_gram_resolventSet_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    resolventSet ℂ (gram lam alpha hlam ha) =
      resolventSet ℂ (outputGram lam alpha hlam ha) := by
  have hs := two_sided_gram_spectrum_eq lam alpha hlam ha
  simpa only [spectrum, compl_inj_iff] using hs

/-- For every positive regularization parameter t, -t is in the
scalar resolvent of the genuine ultraspherical source Gram. -/
theorem source_gram_negative_real_mem_resolventSet
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (t : ℝ) (ht : 0 < t) :
    (-(t : ℂ)) ∈ resolventSet ℂ (gram lam alpha hlam ha) := by
  have hnot : (-(t : ℂ)) ∉ spectrum ℂ (gram lam alpha hlam ha) := by
    intro hmem
    have hnonneg :=
      (two_sided_gram_spectra_nonnegative_real lam alpha hlam ha).1
        (-(t : ℂ)) hmem |>.2
    have : 0 ≤ -t := by simpa using hnonneg
    linarith
  simpa only [spectrum, Set.mem_compl_iff, not_not] using hnot

/-- The same negative real parameters regularize the full
Fock coefficient-side Gram CC†. -/
theorem output_gram_negative_real_mem_resolventSet
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (t : ℝ) (ht : 0 < t) :
    (-(t : ℂ)) ∈ resolventSet ℂ (outputGram lam alpha hlam ha) := by
  rw [← two_sided_gram_resolventSet_eq lam alpha hlam ha]
  exact source_gram_negative_real_mem_resolventSet
    lam alpha hlam ha t ht

#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_resolventSet_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.source_gram_negative_real_mem_resolventSet
#print axioms GegenbauerFock.GeneralUltrasphericalFock.output_gram_negative_real_mem_resolventSet

end GegenbauerFock.GeneralUltrasphericalFock
