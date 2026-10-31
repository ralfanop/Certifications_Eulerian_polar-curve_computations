import GegenbauerFock.UltrasphericalSturmLiouvilleMonicPolynomialSpan
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialDensity

/-!
# V007 — unconditional Hilbert density of genuine Gegenbauer modes

The real polynomial span of the explicitly constructed monic
Gegenbauer modes equals the entire polynomial evaluation domain
in the actual weighted L² Hilbert space. The pre-certified
Weierstrass density of polynomial evaluation then gives dense
linear span of these particular Sturm eigenfunctions.

This establishes completeness of their algebraic linear span in
L², but does NOT yet assert nonzero normalized vectors, a Hilbert
orthonormal basis, or the weighted diagonal operator domain.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- Image of the all-degree Gegenbauer polynomial span under
true weighted-real-L² evaluation equals its full polynomial domain. -/
theorem sturmMonicEigenCandidate_realL2_span_eq_polynomialDomain
    (lam : ℝ) (hlam : 0 < lam) :
    Submodule.span ℝ
      (Set.range (fun n : ℕ =>
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n))) =
      sturmRealPolynomialDomain lam hlam := by
  let F := sturmRealPolynomialLinear lam hlam
  have himage :
      Set.range (fun n : ℕ =>
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n)) =
        F '' Set.range (sturmMonicEigenCandidate lam) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨sturmMonicEigenCandidate lam n, ⟨n, rfl⟩, rfl⟩
    · rintro ⟨p, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
  rw [himage, ← Submodule.map_span,
      sturmMonicEigenCandidate_span_eq_top]
  change Submodule.map F ⊤ = LinearMap.range F
  exact Submodule.map_top

/-- GENUINE weighted L² density of the concrete all-degree
Gegenbauer polynomial eigenfunctions, without completeness
assumptions and without an abstract model Hilbert space. -/
theorem sturmMonicEigenCandidate_realL2_span_dense
    (lam : ℝ) (hlam : 0 < lam) :
    (Submodule.span ℝ
      (Set.range (fun n : ℕ =>
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n)))).topologicalClosure = ⊤ := by
  rw [sturmMonicEigenCandidate_realL2_span_eq_polynomialDomain]
  exact sturmRealPolynomialDomain_dense lam hlam

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_span_eq_polynomialDomain
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_span_dense

end GegenbauerFock.Ultraspherical
