import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventPolynomialEigenmode

/-!
# V007 — explicit all-degree Gegenbauer eigenmodes of the true closed Sturm operator

The finite monic Gegenbauer recurrence gives a genuine polynomial
eigen-equation for each natural degree, and the previously certified
full-L² resolvent bridge sends every such polynomial eigenvector into
the domain of the canonical CLOSED real Sturm operator. This file
instantiates that bridge, without assuming a diagonal Hilbert basis,
nonzero norm, orthogonality, or density of these eigenmodes.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- For every degree, the explicitly given monic Gegenbauer polynomial
belongs to the genuine closed Sturm domain and has exact eigenvalue. -/
theorem sturmRealClosed_monic_all_degree_eigenmode
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) =
        sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n) ∧
      (sturmRealPartialOperator lam hlam).closure x =
        sturmEigenvalue lam n • (x : SturmH lam) := by
  exact sturmRealClosed_polynomial_eigenmode lam hlam
    (sturmMonicEigenCandidate lam n) n
    (sturmMonicEigenCandidate_eigen lam hlam n)

/-- The true everywhere-defined full-L² positive Sturm resolvent acts
diagonally on the explicitly constructed degree-n monic polynomial.
This does not rely on a previously postulated complete eigenbasis. -/
theorem sturmRealPositiveResolventFullCLM_monic_all_degree_eigenmode
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
      (sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n)) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        sturmRealPolynomialLp lam hlam (sturmMonicEigenCandidate lam n) := by
  simpa only [sturmEigenvalue, sub_neg_eq_add] using
    (sturmRealPositiveResolventFullCLM_polynomial_eigenmode
      lam t hlam ht (sturmMonicEigenCandidate lam n) n
      (sturmMonicEigenCandidate_eigen lam hlam n))

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_monic_all_degree_eigenmode
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_monic_all_degree_eigenmode

end GegenbauerFock.Ultraspherical
