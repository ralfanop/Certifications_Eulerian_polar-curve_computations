import GegenbauerFock.UltrasphericalSturmLiouvilleAllMonomialPairs

/-!
# V007 — full polynomial Green matrix form

For real polynomials p and q, the finite double coefficient sum
defines the algebraic Green form induced by the exact monomial
matrix of the ultraspherical differential expression.

It is symmetric by the unconditional Green monomial-pair theorem
for the true Beta-pushforward moment law. The sum is genuinely finite
and ranges over the complete polynomial supports, not truncated degrees.

The remaining analytic bridge must identify this algebraic form with
the actual integral of (L p)(u) q(u) against nu_lambda and then with
the weighted L² Hilbert pairing. No L² self-adjointness is claimed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open Polynomial

/-- Actual all-degree moment matrix contracted against the coefficients
of two real polynomials. -/
noncomputable def sturmPolynomialGreenMatrixForm
    (lam : ℝ) (p q : ℝ[X]) : ℝ :=
  ∑ n ∈ p.support, ∑ m ∈ q.support,
    p.coeff n * q.coeff m * sturmMonomialMomentPair lam n m

/-- Symmetry of the finite polynomial Green coefficient form.
No moment functional or formal inner-product symmetry is postulated. -/
theorem sturmPolynomialGreenMatrixForm_symm
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    sturmPolynomialGreenMatrixForm lam p q =
      sturmPolynomialGreenMatrixForm lam q p := by
  classical
  unfold sturmPolynomialGreenMatrixForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [sturmMonomialMomentPair_symmetric lam hlam n m]
  ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomialGreenMatrixForm_symm

end GegenbauerFock.Ultraspherical
