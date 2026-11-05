import Mathlib

/-!
# V007 — ultraspherical Sturm–Liouville polynomial core

The Gegenbauer differential expression on real polynomials is

  (1 - x²) p''(x) - (2λ + 1) x p'(x).

This module treats the differential expression *on polynomials only*.
It does not assert a self-adjoint unbounded L² realization, any boundary
conditions, or commutation with the Gegenbauer–Fock integral operator.
Those require separate domain-sensitive arguments.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open Polynomial

/-- Algebraic Gegenbauer differential expression on the polynomial core. -/
def sturmPolynomial (lam : ℝ) (p : ℝ[X]) : ℝ[X] :=
  (1 - X ^ 2) * derivative (derivative p) -
    C (2 * lam + 1) * X * derivative p

/-- The constant polynomial is a zero mode of the Gegenbauer expression. -/
theorem sturmPolynomial_C (lam c : ℝ) :
    sturmPolynomial lam (C c) = 0 := by
  simp [sturmPolynomial]

/-- The first-degree polynomial has eigenvalue -(2λ+1). -/
theorem sturmPolynomial_X (lam : ℝ) :
    sturmPolynomial lam X = -(C (2 * lam + 1) * X) := by
  simp [sturmPolynomial]

/-- Additivity on the algebraic polynomial core. -/
theorem sturmPolynomial_add (lam : ℝ) (p q : ℝ[X]) :
    sturmPolynomial lam (p + q) =
      sturmPolynomial lam p + sturmPolynomial lam q := by
  simp only [sturmPolynomial, derivative_add]
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_C
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_X
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_add

end GegenbauerFock.Ultraspherical
