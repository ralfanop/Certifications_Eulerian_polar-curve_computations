import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial
import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventPolynomialEigenmode

/-!
# V007 — unconditional ALL DEGREE concrete Gegenbauer L² eigenmodes

The explicitly constructed finite monic Gegenbauer polynomials are
genuine polynomial eigenfunctions for every natural degree n.
Transporting their unconditional eigen-equation through the already
certified polynomial-to-closed-domain theorem yields true eigenmodes
of the canonical weighted-real-L² Sturm closure and the all-L²
bounded positive resolvent.

No Hilbert orthonormal eigenbasis completeness is assumed or asserted.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Each explicitly constructed degree-n monic Gegenbauer polynomial
belongs to the actual closed Sturm domain with exact eigenvalue. -/
theorem sturmMonicEigenCandidate_closed_domain_eigen
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) =
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n) ∧
      (sturmRealPartialOperator lam hlam).closure x =
        sturmEigenvalue lam n • (x : SturmH lam) :=
  sturmRealClosed_polynomial_eigenmode
    lam hlam (sturmMonicEigenCandidate lam n) n
      (sturmMonicEigenCandidate_eigen lam hlam n)

/-- The TRUE bounded Sturm resolvent acts diagonally on the
CONSTRUCTED polynomial modes for every natural degree. -/
theorem sturmMonicEigenCandidate_full_resolvent_diagonal
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (n : ℕ) :
    sturmRealPositiveResolventFullCLM lam t hlam ht
        (sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n)) =
      (t + (n : ℝ) * ((n : ℝ) + 2 * lam))⁻¹ •
        sturmRealPolynomialLp lam hlam
          (sturmMonicEigenCandidate lam n) := by
  have h := sturmRealPositiveResolventFullCLM_polynomial_eigenmode
    lam t hlam ht (sturmMonicEigenCandidate lam n) n
      (sturmMonicEigenCandidate_eigen lam hlam n)
  have hden :
      t - sturmEigenvalue lam n =
        t + (n : ℝ) * ((n : ℝ) + 2 * lam) := by
    unfold sturmEigenvalue
    ring
  rw [hden] at h
  exact h

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_closed_domain_eigen
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_full_resolvent_diagonal

end GegenbauerFock.Ultraspherical
