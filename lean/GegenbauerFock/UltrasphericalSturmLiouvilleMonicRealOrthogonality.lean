import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenPolynomial
import GegenbauerFock.UltrasphericalSturmLiouvilleRealEigenOrthogonality

/-!
# V007 — unconditional orthogonality of the explicitly constructed modes

Every degree-n monic Gegenbauer polynomial exists by a finite
coefficient recurrence and is an exact Sturm eigenpolynomial.
The genuine weighted-real-L² Green identity then implies
mutual orthogonality of distinct degrees, with no completeness
or abstract eigenfunction existence assumptions.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- Explicit monic Gegenbauer polynomials of different natural
degrees are orthogonal in the ACTUAL weighted real Hilbert L². -/
theorem sturmMonicEigenCandidate_realL2_orthogonal
    (lam : ℝ) (hlam : 0 < lam) (n m : ℕ) (hnm : n ≠ m) :
    inner ℝ
      (sturmRealPolynomialLp lam hlam
        (sturmMonicEigenCandidate lam n))
      (sturmRealPolynomialLp lam hlam
        (sturmMonicEigenCandidate lam m)) = 0 :=
  sturmRealPolynomial_eigen_orthogonal lam hlam
    (sturmMonicEigenCandidate lam n)
    (sturmMonicEigenCandidate lam m)
    n m
    (sturmMonicEigenCandidate_eigen lam hlam n)
    (sturmMonicEigenCandidate_eigen lam hlam m)
    hnm

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_realL2_orthogonal

end GegenbauerFock.Ultraspherical
