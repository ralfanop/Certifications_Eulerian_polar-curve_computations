import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2DenseSpan
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealOrthogonality

/-!
# V007 — all-degree Gegenbauer family is a total orthogonal system

For the genuine ultraspherical weighted real Hilbert L², every
constructed monic Gegenbauer eigenpolynomial is orthogonal to
the other degrees (earlier certified Green identity) and their
real linear span is dense (Weierstrass plus triangularity).
Therefore their common orthogonal complement is exactly zero.

This is a complete ORTHOGONAL SYSTEM claim. An explicitly normalized
Hilbert orthonormal basis requires separate nonzero-norm proofs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- Completeness formulated without normalization: there is no
nonzero L² vector orthogonal to every explicitly constructed
Gegenbauer eigenpolynomial. -/
theorem sturmMonicEigenCandidate_realL2_orthogonalComplement_eq_bot
    (lam : ℝ) (hlam : 0 < lam) :
    (Submodule.span ℝ
      (Set.range (fun n : ℕ =>
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n))))ᗮ = ⊥ := by
  let S : Submodule ℝ (Lp ℝ 2 (measure lam)) :=
    Submodule.span ℝ
      (Set.range (fun n : ℕ =>
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n)))
  have hdense : S.topologicalClosure = ⊤ :=
    sturmMonicEigenCandidate_realL2_span_dense lam hlam
  change Sᗮ = ⊥
  calc
    Sᗮ = S.topologicalClosureᗮ :=
      (Submodule.orthogonal_closure S).symm
    _ = (⊤ : Submodule ℝ (Lp ℝ 2 (measure lam)))ᗮ := by
      rw [hdense]
    _ = ⊥ := Submodule.top_orthogonal_eq_bot

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_orthogonalComplement_eq_bot

end GegenbauerFock.Ultraspherical
