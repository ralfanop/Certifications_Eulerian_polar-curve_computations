import GegenbauerFock.GaussianAreaCoefficientSynthesisL2

/-!
# V007 — the Gaussian Hilbert coefficient synthesis has closed range

The isometric embedding from ℓ² into the full Gaussian weighted
L² space has a complete domain. Its range is therefore closed.
This gives an actual closed Hilbert subspace of Gaussian L²,
containing the synthesized normalized monomial coefficients.

Identifying this range with the ENTIRE holomorphic Gaussian Fock
subspace requires a separate polynomial-density/surjectivity proof.
Closed range alone is not that identification.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The range of the genuine infinite ℓ² Gaussian coefficient
synthesis is a closed subset of the completed weighted L² space. -/
theorem coefficientSynthesisL2_range_isClosed
    (alpha : ℝ) (ha : 0 < alpha) :
    IsClosed (Set.range (coefficientSynthesisL2 alpha ha)) := by
  exact (coefficientSynthesisL2 alpha ha).isometry.isUniformInducing.isComplete_range.isClosed

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_range_isClosed

end GegenbauerFock.GaussianArea
