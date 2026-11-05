import GegenbauerFock.WeightedMoments
import GegenbauerFock.InfiniteFockAnalysis
import GegenbauerFock.HilbertGram

/-!
# V007: the actual bounded ultraspherical L² -> infinite Fock-coordinate operator

Uses the *concrete* probability measure μ with support in [-1,1].
In particular μ := Ultraspherical.measure λ (λ>0) meets these hypotheses.
Its nth coefficient is the normalized Fourier moment
  (i^n / (2^n α^(n/2) sqrt(n!))) × ∫ u^n f(u) dμ(u),
in the verified L² Riesz model.

This module establishes the infinite-dimensional bounded operator,
its coordinate values, and its actual Hilbert-space adjoint and Gram
quadratic form. It DOES NOT YET establish the Gaussian holomorphic
Fock isometry, the analytic integral-transform identification, the
operator's exact Hilbert-Schmidt norm, or its compactness.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.ConcreteFock

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]
variable (hsupport : ∀ᵐ u ∂μ, |u| ≤ (1 : ℝ))
variable (alpha : ℝ) (ha : 0 < alpha)

include hsupport

/-- Genuine bounded map from L²(μ) into infinite-dimensional Fock ℓ²,
with the actual factorially weighted monomial Riesz functionals. -/
noncomputable def operator :
    Lp ℂ 2 μ →L[ℂ] InfiniteAnalysis.FockCoefficients :=
  InfiniteAnalysis.bounded
    (fun n => WeightedMoments.coefficient μ hsupport alpha n)
    (WeightedMoments.coefficient_norm_sq_summable μ hsupport alpha ha)

/-- Each coordinate is the specified weighted L² monomial moment. -/
theorem operator_coefficient (f : Lp ℂ 2 μ) (n : ℕ) :
    operator μ hsupport alpha ha f n =
      WeightedMoments.coefficient μ hsupport alpha n f := by
  exact InfiniteAnalysis.bounded_apply
    (fun n => WeightedMoments.coefficient μ hsupport alpha n)
    (WeightedMoments.coefficient_norm_sq_summable μ hsupport alpha ha)
    f n

/-- The exact bounded-operator quadratic energy estimate. -/
theorem operator_norm_sq_bound (f : Lp ℂ 2 μ) :
    ‖operator μ hsupport alpha ha f‖ ^ 2 ≤
      (∑' n, ‖WeightedMoments.coefficient μ hsupport alpha n‖ ^ 2) *
        ‖f‖ ^ 2 := by
  exact InfiniteAnalysis.norm_sq_le
    (fun n => WeightedMoments.coefficient μ hsupport alpha n)
    (WeightedMoments.coefficient_norm_sq_summable μ hsupport alpha ha) f

/-- This is the actual adjoint of the above concrete bounded operator,
not a merely hypothetical adjoint for an unspecified map. -/
noncomputable def adjoint :
    InfiniteAnalysis.FockCoefficients →L[ℂ] Lp ℂ 2 μ :=
  (operator μ hsupport alpha ha).adjoint

theorem adjoint_pairing (F : InfiniteAnalysis.FockCoefficients)
    (f : Lp ℂ 2 μ) :
    inner ℂ (adjoint μ hsupport alpha ha F) f =
      inner ℂ F (operator μ hsupport alpha ha f) := by
  exact (operator μ hsupport alpha ha).adjoint_inner_left f F

/-- Concrete Gram C†C. -/
noncomputable def gram : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  HilbertGram.gram (operator μ hsupport alpha ha)

theorem gram_adjoint :
    (gram μ hsupport alpha ha).adjoint =
      gram μ hsupport alpha ha := by
  exact HilbertGram.gram_adjoint (operator μ hsupport alpha ha)

theorem gram_nonneg (f : Lp ℂ 2 μ) :
    0 ≤ RCLike.re (inner ℂ (gram μ hsupport alpha ha f) f) := by
  exact HilbertGram.gram_re_nonneg (operator μ hsupport alpha ha) f

theorem gram_norm_sq (f : Lp ℂ 2 μ) :
    ‖operator μ hsupport alpha ha f‖ ^ 2 =
      RCLike.re (inner ℂ (gram μ hsupport alpha ha f) f) := by
  exact HilbertGram.gram_norm_sq (operator μ hsupport alpha ha) f

#print axioms GegenbauerFock.ConcreteFock.operator_coefficient
#print axioms GegenbauerFock.ConcreteFock.operator_norm_sq_bound
#print axioms GegenbauerFock.ConcreteFock.adjoint_pairing
#print axioms GegenbauerFock.ConcreteFock.gram_adjoint
#print axioms GegenbauerFock.ConcreteFock.gram_nonneg
#print axioms GegenbauerFock.ConcreteFock.gram_norm_sq

end GegenbauerFock.ConcreteFock
