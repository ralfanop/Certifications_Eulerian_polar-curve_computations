import GegenbauerFock.GaussianAreaL2Orthonormality
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# V007 — real orthonormal monomials in completed Gaussian L²(ℂ)

The normalized complex monomials are actual L² vectors, with the
full pointwise Gaussian Radon–Nikodym density and rigorous Lebesgue
integrability. Their L² inner products are the exact Kronecker
delta, hence they form a genuine orthonormal family in the
completed weighted complex Hilbert space.

Completeness in the holomorphic subspace and surjectivity of an
isometry from the full coefficient Hilbert space remain unproved.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Actual normalized entire monomials form an orthonormal family in
the completed complex Gaussian L² space for every alpha > 0. -/
theorem orthonormal_normalizedMonomialL2Vector
    (alpha : ℝ) (ha : 0 < alpha) :
    Orthonormal ℂ
      (fun n : ℕ => normalizedMonomialL2Vector alpha ha n) := by
  classical
  rw [orthonormal_iff_ite]
  intro m n
  exact inner_normalizedMonomialL2Vector alpha ha m n

#print axioms GegenbauerFock.GaussianArea.orthonormal_normalizedMonomialL2Vector

end GegenbauerFock.GaussianArea
