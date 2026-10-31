import GegenbauerFock.GegenbauerIntrinsicEntireGramZeroSpectrum
import GegenbauerFock.TwoSidedGramContinuousSpectrum
import GegenbauerFock.TwoSidedGramSingularWeylZero
import GegenbauerFock.TwoSidedGramInverseInstability

/-!
# V007 — continuous spectral zero and inverse instability of intrinsic Fock Gram

The genuine source Gram formed using the complete intrinsic holomorphic
Gaussian L² Bargmann–Fock codomain is *exactly* the already-certified
Gegenbauer source Gram on ultraspherical L². Consequently, zero is in
its continuous spectrum, and a unit-norm singular Weyl sequence tends
weakly to zero while its Gram images tend strongly to zero.

The Gram has dense, proper, nonclosed range. No finite bound controls
the inverse on the range: for each K≥0 an actual source vector violates
the corresponding reconstruction estimate. The statements are about
the genuine infinite-dimensional source Hilbert space, not a finite
matrix, nor the full Gaussian area L² ambient space.
-/

noncomputable section
open MeasureTheory Filter
open scoped NNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Zero is an actual continuous spectral point of the intrinsic
holomorphic source Gram, not an eigenvalue or a residual spectral point. -/
theorem C_intrinsicEntire_gram_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsContinuousSpectralPointAtZero
      (C_intrinsicEntire_gram lam alpha hlam ha) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact source_gram_zero_continuous_spectrum lam alpha hlam ha

/-- Singular Weyl sequence for the true intrinsic Gaussian Fock
source Gram: normalized vectors, strongly vanishing images, and
weak convergence against every complex Hilbert test vector. -/
theorem C_intrinsicEntire_gram_has_singular_weyl_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      IsSingularWeylSequenceAtZero
        (C_intrinsicEntire_gram lam alpha hlam ha) u := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact sourceGram_has_singular_weyl_sequence_at_zero lam alpha hlam ha

/-- Even though the source Gram is injective, its actual range is
nonclosed in the ultraspherical L² Hilbert space. -/
theorem C_intrinsicEntire_gram_range_not_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsClosed
      ((C_intrinsicEntire_gram lam alpha hlam ha).range :
        Set (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact gram_range_not_closed lam alpha hlam ha

/-- For every finite reconstruction constant K≥0, some genuine
ultraspherical source vector violates the inverse estimate. -/
theorem C_intrinsicEntire_gram_inverse_unbounded_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      (K : ℝ) * ‖C_intrinsicEntire_gram lam alpha hlam ha f‖ < ‖f‖ := by
  rw [C_intrinsicEntire_gram_eq lam alpha hlam ha]
  exact sourceGram_inverse_unbounded_on_range lam alpha hlam ha K

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_zero_continuous_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_has_singular_weyl_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_range_not_closed
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_inverse_unbounded_on_range

end GegenbauerFock.GeneralUltrasphericalFock
