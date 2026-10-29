import GegenbauerFock.UltrasphericalSturmLiouvilleLinearMap

/-!
# V007 — actual polynomial differential operator as finite monomial sum

The already Lean-certified real-linear map L_lambda is applied
to the exact finite expansion of an arbitrary polynomial
p = sum_n coeff(p,n) X^n. All coefficients are actual polynomial
coefficients, and no formally truncated degree is assumed.

This is the algebraic prerequisite for transferring the genuine
monomial Green integrals to arbitrary polynomial inputs.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- A polynomial's exact finite monomial expansion in real
scalar-multiplication notation. -/
theorem sturmPolynomial_true_monomial_expansion
    (p : ℝ[X]) :
    (∑ n ∈ p.support, p.coeff n • (X ^ n : ℝ[X])) = p := by
  classical
  simpa only [Polynomial.sum, smul_eq_C_mul] using
    (Polynomial.sum_C_mul_X_pow_eq p)

/-- The genuine Gegenbauer polynomial differential operator commutes
with the complete finite monomial expansion. -/
theorem sturmPolynomial_apply_sum_monomials
    (lam : ℝ) (p : ℝ[X]) :
    sturmPolynomial lam p =
      ∑ n ∈ p.support,
        C (p.coeff n) * sturmPolynomial lam (X ^ n) := by
  classical
  calc
    sturmPolynomial lam p = sturmPolynomialLinear lam p := rfl
    _ = sturmPolynomialLinear lam
        (∑ n ∈ p.support, p.coeff n • (X ^ n : ℝ[X])) := by
      rw [sturmPolynomial_true_monomial_expansion]
    _ = ∑ n ∈ p.support,
          C (p.coeff n) * sturmPolynomial lam (X ^ n) := by
      simp only [map_sum, sturmPolynomialLinear_apply, smul_eq_C_mul]
      apply Finset.sum_congr rfl
      intro n hn
      change sturmPolynomial lam ((p.coeff n) • (X ^ n)) =
        (p.coeff n) • sturmPolynomial lam (X ^ n)
      exact sturmPolynomial_smul lam (p.coeff n) (X ^ n)

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_true_monomial_expansion
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_apply_sum_monomials

end GegenbauerFock.Ultraspherical
