import GegenbauerFock.UltrasphericalSturmLiouvilleFullGreenIntegral

/-!
# V007 — exact polynomial Leibniz energy formula for Gegenbauer Sturm L

The algebraic differential expression satisfies the exact carré
du champ / square product identity

  Lλ(p²) = 2 p Lλ p + 2 (1-X²) (p')²

for ALL real polynomials and parameters λ. Together with the true
weighted Green identity and the actual support [-1,1] of νλ,
this makes the real polynomial Sturm quadratic form nonpositive.

This first module certifies the pure exact polynomial identity and
the vanishing of the weighted integral of Lλ p.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- Exact polynomial carré-du-champ identity for the genuine
Gegenbauer differential expression, no integrals or formal series. -/
theorem sturmPolynomial_square_leibniz
    (lam : ℝ) (p : ℝ[X]) :
    sturmPolynomial lam (p * p) =
      C (2 : ℝ) * p * sturmPolynomial lam p +
        C (2 : ℝ) * (1 - X ^ 2) *
          derivative p * derivative p := by
  unfold sturmPolynomial
  simp only [derivative_mul, derivative_add]
  have htwo : (C (2 : ℝ) : ℝ[X]) = 2 := by norm_num
  rw [htwo]
  ring

/-- Every actual weighted ultraspherical probability integral of the
Gegenbauer differential expression on a real polynomial is zero.
This is a consequence of the certified genuine Green identity. -/
theorem sturmPolynomial_integral_zero
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    (∫ u : ℝ, (sturmPolynomial lam p).eval u ∂(measure lam)) = 0 := by
  have hconst : sturmPolynomial lam (1 : ℝ[X]) = 0 := by
    simpa using (sturmPolynomial_C lam (1 : ℝ))
  have hgreen :=
    sturmPolynomial_green_integral_symmetric lam hlam p (1 : ℝ[X])
  simpa [hconst] using hgreen

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_square_leibniz
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_integral_zero

end GegenbauerFock.Ultraspherical
