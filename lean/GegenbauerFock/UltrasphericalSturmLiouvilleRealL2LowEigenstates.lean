import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialLinear
import GegenbauerFock.UltrasphericalSturmLiouvilleQuadratic
import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# V007 — genuine real weighted-L² low Gegenbauer polynomial eigenvectors

The algebraically certified constant, linear and quadratic
Gegenbauer eigenpolynomials are transported into actual weighted L²
polynomial vectors for the Beta-pushforward ultraspherical law.

These are exact eigen-relations for the polynomial differential
expression represented in L², not a claim about the full unbounded
operator's self-adjointness, eigenbasis completeness or spectral domain.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- The degree-zero mode is the genuine real L² vacuum polynomial. -/
theorem sturmRealPolynomialLp_constant_mode
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPolynomialLp lam hlam
      (sturmPolynomial lam (1 : ℝ[X])) =
      sturmEigenvalue lam 0 •
        sturmRealPolynomialLp lam hlam (1 : ℝ[X]) := by
  have hconst : sturmPolynomial lam (1 : ℝ[X]) = 0 := by
    simpa using (sturmPolynomial_C lam 1)
  rw [hconst, sturmEigenvalue_zero]
  change sturmRealPolynomialLinear lam hlam (0 : ℝ[X]) =
    (0 : ℝ) • sturmRealPolynomialLp lam hlam (1 : ℝ[X])
  simp

/-- Degree-one true real weighted-L² eigen-relation. -/
theorem sturmRealPolynomialLp_linear_mode
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPolynomialLp lam hlam (sturmPolynomial lam X) =
      sturmEigenvalue lam 1 • sturmRealPolynomialLp lam hlam X := by
  have hlinear :
      sturmPolynomial lam X = (sturmEigenvalue lam 1) • X := by
    rw [sturmPolynomial_X]
    simp only [sturmEigenvalue, smul_eq_C_mul]
    push_cast
    ring
  rw [hlinear, sturmRealPolynomialLp_smul]

/-- The actual degree-two real weighted-L² Gegenbauer eigenvector,
retaining the exact polynomial normalization 2(λ+1)X²-1. -/
theorem sturmRealPolynomialLp_quadratic_mode
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPolynomialLp lam hlam
      (sturmPolynomial lam (sturmQuadratic lam)) =
      sturmEigenvalue lam 2 •
        sturmRealPolynomialLp lam hlam (sturmQuadratic lam) := by
  have hd : sturmEigenvalue lam 2 = -(4 * (lam + 1)) := by
    unfold sturmEigenvalue
    push_cast
    ring
  rw [sturmPolynomial_quadratic_eigen, hd]
  change sturmRealPolynomialLp lam hlam
      ((-(4 * (lam + 1))) • sturmQuadratic lam) =
        (-(4 * (lam + 1))) • sturmRealPolynomialLp lam hlam
          (sturmQuadratic lam)
  exact sturmRealPolynomialLp_smul lam hlam
    (-(4 * (lam + 1))) (sturmQuadratic lam)

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_constant_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_linear_mode
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_quadratic_mode

end GegenbauerFock.Ultraspherical
