import GegenbauerFock.UltrasphericalSturmLiouvilleMonomials

/-!
# V007 — exact algebraic Green cancellation for ultraspherical monomial moments

For the Gegenbauer differential expression on the polynomial core,
the two monomial matrix elements are identical if the weighted
moments satisfy the exact shifted two-step ultraspherical recurrence.

This isolates the purely algebraic part of Green symmetry.
The actual two-step moment identity for the Beta-pushforward measure,
the density change-of-variables, endpoint integration by parts, and
symmetry of the unbounded operator on weighted L² remain separate proofs.
There are no analytic/domain assertions in this module.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

/-- Cancellation of two off-diagonal monomial matrix coefficients,
conditional on the exact ultraspherical two-step moment recurrence.
The real parameters a,b represent the degrees minus two. -/
theorem green_coefficient_identity
    (lam a b momentLow momentHigh : ℝ)
    (hrec : (a + b + 4 + 2 * lam) * momentHigh =
       (a + b + 3) * momentLow) :
    (a + 2) * (a + 1) * momentLow -
        (a + 2) * (a + 2 * lam + 2) * momentHigh =
      (b + 2) * (b + 1) * momentLow -
        (b + 2) * (b + 2 * lam + 2) * momentHigh := by
  linear_combination (b - a) * hrec

/-- Exact conditional Green symmetry for monomials of degrees a+2,b+2
in terms of a common moment sequence. Multiplicities and the
two-step recurrence are not concealed in a generic symmetry hypothesis. -/
theorem green_high_monomials
    (lam : ℝ) (moment : ℕ → ℝ) (a b : ℕ)
    (hrec :
      ((((a + b + 4 : ℕ) : ℝ) + 2 * lam) *
         moment (a + b + 4)) =
      (((a + b + 3 : ℕ) : ℝ) * moment (a + b + 2))) :
    (((a + 2 : ℕ) : ℝ) * ((a + 1 : ℕ) : ℝ)) * moment (a + b + 2) -
        (((a + 2 : ℕ) : ℝ) * (((a + 2 : ℕ) : ℝ) + 2 * lam)) *
          moment (a + b + 4) =
      (((b + 2 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ)) * moment (a + b + 2) -
        (((b + 2 : ℕ) : ℝ) * (((b + 2 : ℕ) : ℝ) + 2 * lam)) *
          moment (a + b + 4) := by
  have hreal :
      ((a : ℝ) + (b : ℝ) + 4 + 2 * lam) * moment (a + b + 4) =
        ((a : ℝ) + (b : ℝ) + 3) * moment (a + b + 2) := by
    convert hrec using 1 <;> push_cast <;> ring
  have hgreen :=
    green_coefficient_identity lam (a : ℝ) (b : ℝ)
      (moment (a + b + 2)) (moment (a + b + 4)) hreal
  convert hgreen using 1 <;> push_cast <;> ring

#print axioms GegenbauerFock.Ultraspherical.green_coefficient_identity
#print axioms GegenbauerFock.Ultraspherical.green_high_monomials

end GegenbauerFock.Ultraspherical
