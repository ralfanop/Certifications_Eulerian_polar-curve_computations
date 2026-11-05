import GegenbauerFock.GaussianAreaCoefficientSynthesisClosedRange

/-!
# V007 — exact Gaussian L² coefficient recovery

The normalized monomial family gives an isometric synthesis map from
complex ℓ² to the actual weighted Gaussian L² space. This module
certifies the image of individual coefficient basis vectors, the full
infinite Gram pairing, and the exact recovery of each ℓ² coefficient
through the L² inner product with its normalized monomial.

These statements do not assume polynomial density in the ambient
holomorphic Gaussian L² space and do not claim that the synthesis map
is onto that space.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- A single unit coefficient synthesizes the corresponding actual
normalized Gaussian monomial in the completed weighted L² space. -/
theorem coefficientSynthesisL2_single
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    coefficientSynthesisL2 alpha ha (lp.single 2 n (1 : ℂ)) =
      normalizedMonomialL2Vector alpha ha n := by
  classical
  change
    ((orthonormal_normalizedMonomialL2Vector alpha ha).orthogonalFamily).linearIsometry
      (lp.single 2 n (1 : ℂ)) = _
  rw [OrthogonalFamily.linearIsometry_apply_single]
  simp only [LinearIsometry.toSpanSingleton_apply, one_smul]

/-- Full, infinite coefficient Gram identity for actual Gaussian L²
vectors, not just finite sums or a postulated formal Gram matrix. -/
theorem coefficientSynthesisL2_inner
    (alpha : ℝ) (ha : 0 < alpha)
    (a b : lp (fun _ : ℕ => ℂ) 2) :
    inner ℂ (coefficientSynthesisL2 alpha ha a)
      (coefficientSynthesisL2 alpha ha b) = inner ℂ a b := by
  exact (coefficientSynthesisL2 alpha ha).inner_map_map a b

/-- Each complex coefficient of a synthesized Gaussian L² vector is
recovered exactly by its inner product with the normalized monomial. -/
theorem coefficientSynthesisL2_coefficient
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
      (coefficientSynthesisL2 alpha ha a) = a n := by
  rw [← coefficientSynthesisL2_single alpha ha n]
  rw [coefficientSynthesisL2_inner alpha ha]
  rw [lp.inner_single_left]
  simp

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_single
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_inner
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_coefficient

end GegenbauerFock.GaussianArea
