import GegenbauerFock.GramIntegralL2

/-!
# V007: explicit polynomial representatives for weighted Fock-row adjoints

This is the algebraic kernel needed to turn the convergent
L²-adjoint row expansion into a pointwise analytic power series.
Complex conjugation is handled in Mathlib's conjugate-first convention.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.AdjointPolynomial

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))

/-- The true Hilbert adjoint of each weighted moment row returns
the conjugated complex weight multiplied by its L² monomial representer. -/
theorem coefficient_adjoint_explicit (alpha : ℝ) (n : ℕ) (a : ℂ) :
    (WeightedMoments.coefficient μ hsupport alpha n).adjoint a =
      (star (WeightedMoments.complexWeight alpha n) * a) •
        WeightedMoments.monomial μ hsupport n := by
  apply ext_inner_right ℂ
  intro f
  rw [(WeightedMoments.coefficient μ hsupport alpha n).adjoint_inner_left f a]
  change inner ℂ
      ((star (WeightedMoments.complexWeight alpha n) * a) •
        WeightedMoments.monomial μ hsupport n) f =
      inner ℂ a
        (WeightedMoments.complexWeight alpha n *
          inner ℂ (WeightedMoments.monomial μ hsupport n) f)
  simp [inner_smul_left, RCLike.inner_apply', map_mul,
    mul_comm, mul_left_comm, mul_assoc]

#print axioms GegenbauerFock.AdjointPolynomial.coefficient_adjoint_explicit

end GegenbauerFock.AdjointPolynomial
