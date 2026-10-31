import GegenbauerFock.ConcreteFockOperator

/-!
# V007: explicit adjoint on the canonical Fock coordinate basis

The true adjoint of the concrete L²-to-ℓ² Gegenbauer coefficient
operator is evaluated exactly on every finitely supported coordinate
vector. For a single coordinate e_n*a, its adjoint is the already
proved Riesz adjoint of the corresponding weighted monomial moment
functional, without invoking any formal unbounded operator.

The general Fock evaluation formula at -iu/(2α) will then follow
from the dense span of these coordinate vectors together with the
Gaussian holomorphic Fock reconstruction, which is a separate task.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.FockAdjointBasis

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))
variable (alpha : ℝ) (ha : 0 < alpha)

include hsupport

/-- Exact Hilbert adjoint on a single Fock coordinate, every n and a. -/
theorem adjoint_single (n : ℕ) (a : ℂ) :
    (ConcreteFock.operator μ hsupport alpha ha).adjoint
      (lp.single 2 n a) =
      (WeightedMoments.coefficient μ hsupport alpha n).adjoint a := by
  apply ext_inner_right ℂ
  intro f
  rw [(ConcreteFock.operator μ hsupport alpha ha).adjoint_inner_left f (lp.single 2 n a)]
  rw [(WeightedMoments.coefficient μ hsupport alpha n).adjoint_inner_left f a]
  rw [lp.inner_single_left]
  exact congrArg (inner ℂ a)
    (ConcreteFock.operator_coefficient μ hsupport alpha ha f n)

/-- The normalized canonical coefficient vector is sent to the
precise Riesz representer of the corresponding n-th moment row. -/
theorem adjoint_basis (n : ℕ) :
    (ConcreteFock.operator μ hsupport alpha ha).adjoint
      (lp.single 2 n (1 : ℂ)) =
      (WeightedMoments.coefficient μ hsupport alpha n).adjoint 1 :=
  adjoint_single μ hsupport alpha ha n 1

#print axioms GegenbauerFock.FockAdjointBasis.adjoint_single
#print axioms GegenbauerFock.FockAdjointBasis.adjoint_basis

end GegenbauerFock.FockAdjointBasis
