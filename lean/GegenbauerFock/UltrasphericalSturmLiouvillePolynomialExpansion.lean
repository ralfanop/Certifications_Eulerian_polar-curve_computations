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
  have hsum (s : Finset ℕ) :
      sturmPolynomial lam
          (∑ n ∈ s, p.coeff n • (X ^ n : ℝ[X])) =
        ∑ n ∈ s, C (p.coeff n) * sturmPolynomial lam (X ^ n) := by
    induction s using Finset.induction_on with
    | empty =>
        simp [sturmPolynomial]
    | @insert n s hn ih =>
        simp only [Finset.sum_insert hn]
        rw [sturmPolynomial_add, sturmPolynomial_smul, ih]
        simp only [smul_eq_C_mul]
  calc
    sturmPolynomial lam p =
        sturmPolynomial lam
          (∑ n ∈ p.support, p.coeff n • (X ^ n : ℝ[X])) := by
      rw [sturmPolynomial_true_monomial_expansion]
    _ = ∑ n ∈ p.support,
          C (p.coeff n) * sturmPolynomial lam (X ^ n) :=
      hsum p.support

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_true_monomial_expansion
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_apply_sum_monomials

end GegenbauerFock.Ultraspherical
