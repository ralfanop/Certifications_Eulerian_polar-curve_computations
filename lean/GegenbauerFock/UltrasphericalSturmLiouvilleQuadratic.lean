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
  have hs : (2 : ℝ) * (2 + 2 * lam) = 4 * (lam + 1) := by ring
  have htwo :
      sturmPolynomial lam (X ^ 2) =
        C (2 : ℝ) - C (4 * (lam + 1)) * X ^ 2 := by
    simpa only [Nat.zero_add, Nat.cast_ofNat, Nat.cast_one, pow_zero, mul_one, hs]
      using (sturmPolynomial_X_pow_succ_succ lam 0)
  have hone : sturmPolynomial lam (1 : ℝ[X]) = 0 := by
    simpa using (sturmPolynomial_C lam 1)
  have hquad :
      sturmQuadratic lam =
        (2 * (lam + 1)) • (X ^ 2 : ℝ[X]) - 1 := by
    simp only [sturmQuadratic, smul_eq_C_mul]
  have hcoeff :
      C (2 * (lam + 1)) * C (2 : ℝ) = C (4 * (lam + 1)) := by
    rw [← map_mul]
    congr 1
    ring
  calc
    sturmPolynomial lam (sturmQuadratic lam) =
        C (2 * (lam + 1)) *
          (C (2 : ℝ) - C (4 * (lam + 1)) * X ^ 2) := by
      rw [hquad, sturmPolynomial_sub, sturmPolynomial_smul, hone]
      simp only [sub_zero, smul_eq_C_mul]
      rw [htwo]
    _ = C (-(4 * (lam + 1))) * sturmQuadratic lam := by
      rw [sturmQuadratic, map_neg]
      calc
        C (2 * (lam + 1)) *
            (C (2 : ℝ) - C (4 * (lam + 1)) * X ^ 2) =
          C (2 * (lam + 1)) * C (2 : ℝ) -
            (C (2 * (lam + 1)) * C (4 * (lam + 1))) * X ^ 2 := by ring
        _ = C (4 * (lam + 1)) -
            (C (2 * (lam + 1)) * C (4 * (lam + 1))) * X ^ 2 := by rw [hcoeff]
        _ = -C (4 * (lam + 1)) *
            (C (2 * (lam + 1)) * X ^ 2 - 1) := by ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_quadratic_eigen

end GegenbauerFock.Ultraspherical
