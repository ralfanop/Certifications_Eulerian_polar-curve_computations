import GegenbauerFock.UltrasphericalSturmLiouvilleMonomials

/-!
# V007 — Algebraic linear operator on the Gegenbauer polynomial core

The ultraspherical differential expression is an actual real-linear
endomorphism of the polynomial algebra. This does not construct a closed
or self-adjoint operator on weighted L², nor assert any boundary condition.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open Polynomial

/-- The genuine real-linear Gegenbauer differential operator restricted
to the polynomial core. -/
def sturmPolynomialLinear (lam : ℝ) : ℝ[X] →ₗ[ℝ] ℝ[X] where
  toFun := sturmPolynomial lam
  map_add' := by
    intro p q
    exact sturmPolynomial_add lam p q
  map_smul' := by
    intro c p
    exact sturmPolynomial_smul lam c p

@[simp] theorem sturmPolynomialLinear_apply (lam : ℝ) (p : ℝ[X]) :
    sturmPolynomialLinear lam p = sturmPolynomial lam p := rfl

@[simp] theorem sturmPolynomialLinear_C (lam c : ℝ) :
    sturmPolynomialLinear lam (C c) = 0 := by
  change sturmPolynomial lam (C c) = 0
  exact sturmPolynomial_C lam c

/-- Exact lower triangular action of the real-linear map on all
monomials with degree at least two. -/
theorem sturmPolynomialLinear_X_pow_succ_succ (lam : ℝ) (n : ℕ) :
    sturmPolynomialLinear lam (X ^ (n + 2)) =
      C (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) * X ^ n -
      C (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 2 * lam)) *
        X ^ (n + 2) := by
  exact sturmPolynomial_X_pow_succ_succ lam n

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomialLinear_apply
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomialLinear_C
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomialLinear_X_pow_succ_succ

end GegenbauerFock.Ultraspherical
