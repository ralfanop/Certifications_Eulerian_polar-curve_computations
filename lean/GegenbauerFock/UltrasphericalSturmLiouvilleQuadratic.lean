import GegenbauerFock.UltrasphericalSturmLiouvilleMonomials

/-!
# V007 — first nonconstant even Gegenbauer eigenpolynomial

This is a purely algebraic polynomial-core eigenvector, not a claim
of self-adjointness of any unbounded weighted L² operator.
The unnormalized quadratic polynomial
  2 (λ+1) X² - 1
has eigenvalue -4 (λ+1) for the ultraspherical differential expression.
No division by λ+1 is required.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open Polynomial

/-- The degree-two ultraspherical polynomial, without a denominator. -/
def sturmQuadratic (lam : ℝ) : ℝ[X] :=
  C (2 * (lam + 1)) * X ^ 2 - 1

/-- Exact degree-two Gegenbauer eigen-equation on the polynomial core. -/
theorem sturmPolynomial_quadratic_eigen (lam : ℝ) :
    sturmPolynomial lam (sturmQuadratic lam) =
      C (-(4 * (lam + 1))) * sturmQuadratic lam := by
  have htwo := sturmPolynomial_X_pow_succ_succ lam 0
  norm_num at htwo
  have hone : sturmPolynomial lam (1 : ℝ[X]) = 0 := by
    simpa using sturmPolynomial_C lam (1 : ℝ)
  have hscale :
      sturmPolynomial lam (C (2 * (lam + 1)) * X ^ 2) =
        C (2 * (lam + 1)) * sturmPolynomial lam (X ^ 2) := by
    simpa only [smul_eq_C_mul] using
      (sturmPolynomial_smul lam (2 * (lam + 1)) (X ^ 2))
  change sturmPolynomial lam
    (C (2 * (lam + 1)) * X ^ 2 - (1 : ℝ[X])) =
    C (-(4 * (lam + 1))) * (C (2 * (lam + 1)) * X ^ 2 - 1)
  rw [sturmPolynomial_sub, hone, sub_zero, hscale, htwo]
  norm_num [map_add, map_mul, map_neg]
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_quadratic_eigen

end GegenbauerFock.Ultraspherical
