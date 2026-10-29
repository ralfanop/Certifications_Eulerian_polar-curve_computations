import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialCore

/-!
# V007 — Gegenbauer Sturm–Liouville monomial action and linearity

For the genuine algebraic polynomial differential expression
  L_λ p = (1-X²)p'' -(2λ+1)Xp',
prove its action on every monomial of degree at least two:
  L_λ (X^(n+2)) =
    (n+2)(n+1) X^n -(n+2)(n+2λ+2) X^(n+2).

Together with the previously certified constant and X cases,
this is the exact triangular action on the full polynomial core.
It is NOT a claim about closure, boundary conditions, essential
self-adjointness, or a differential operator on all L².
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open Polynomial

/-- Real scalar linearity of the ultraspherical differential expression. -/
theorem sturmPolynomial_smul (lam c : ℝ) (p : ℝ[X]) :
    sturmPolynomial lam (c • p) = c • sturmPolynomial lam p := by
  simp only [sturmPolynomial, derivative_smul, smul_sub]
  simp only [smul_eq_C_mul]
  ring

/-- Subtraction compatibility of the polynomial Gegenbauer expression. -/
theorem sturmPolynomial_sub (lam : ℝ) (p q : ℝ[X]) :
    sturmPolynomial lam (p - q) =
      sturmPolynomial lam p - sturmPolynomial lam q := by
  simp only [sturmPolynomial, derivative_sub]
  ring

/-- Exact lower-triangular monomial rule for all degrees n+2. -/
theorem sturmPolynomial_X_pow_succ_succ (lam : ℝ) (n : ℕ) :
    sturmPolynomial lam (X ^ (n + 2)) =
      C (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) * X ^ n -
      C (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) + 2 * lam)) *
        X ^ (n + 2) := by
  have hfirst :
      derivative (X ^ (n + 2) : ℝ[X]) =
        C (((n + 2 : ℕ) : ℝ)) * X ^ (n + 1) := by
    convert (derivative_X_pow_succ (R := ℝ) (n + 1)) using 1 <;>
      push_cast <;> ring
  have hsecond :
      derivative (derivative (X ^ (n + 2) : ℝ[X])) =
        C (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ)) * X ^ n := by
    rw [hfirst, derivative_C_mul_X_pow]
    simp only [Nat.add_sub_cancel]
  unfold sturmPolynomial
  rw [hsecond, hfirst]
  have hp1 : (X : ℝ[X]) ^ (n + 1) = X ^ n * X := by
    rw [pow_succ]
  have hp2 : (X : ℝ[X]) ^ (n + 2) = X ^ n * X ^ 2 := by
    rw [pow_add]
  rw [hp1, hp2]
  push_cast
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_smul
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_sub
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_X_pow_succ_succ

end GegenbauerFock.Ultraspherical
