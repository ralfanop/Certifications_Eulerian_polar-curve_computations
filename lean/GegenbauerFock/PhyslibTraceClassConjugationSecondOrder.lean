import GegenbauerFock.PhyslibTraceClassConjugationPolarizedOperator

/-!
# V007 — exact second-order expansion of trace-class conjugation

For the genuine CFC Schatten S₁ endomorphism
Phi_U(T) = U† T U, perturbing U by a bounded K gives an exact
quadratic expansion, with a remainder of norm at most ‖K‖².
The statements concern true trace-normed operator actions, with no
positivity, finite-rank or coisometry assumption.

The remainder certificate is a precursor to, but is not by itself,
a Lean formalization of real Fréchet differentiability.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact expansion of a two-sided S₁ action in both bounded
multipliers. This is an equality of continuous linear maps on S₁. -/
theorem sandwichContinuous_add_add_exact_v007
    (A B C D : H →L[ℂ] H) :
    sandwichContinuous (A + C) (B + D) =
      sandwichContinuous A B + sandwichContinuous A D +
        sandwichContinuous C B + sandwichContinuous C D := by
  apply ContinuousLinearMap.ext
  intro T
  apply Subtype.ext
  change (A + C) * T.1 * (B + D) =
    (A * T.1 * B + A * T.1 * D) +
      C * T.1 * B + C * T.1 * D
  simp only [mul_add, add_mul, mul_assoc]
  abel

/-- Exact order-two expansion of Phi_(U+K), including the
mixed first-order terms, on the full trace-class space. -/
theorem conjugationContinuous_secondOrder_expand_v007
    (U K : H →L[ℂ] H) :
    sandwichContinuous (U + K).adjoint (U + K) =
      sandwichContinuous U.adjoint U +
      sandwichContinuous U.adjoint K +
      sandwichContinuous K.adjoint U +
      sandwichContinuous K.adjoint K := by
  have hAdj : (U + K).adjoint = U.adjoint + K.adjoint := by
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact star_add U K
  rw [hAdj]
  exact sandwichContinuous_add_add_exact_v007 U.adjoint U K.adjoint K

/-- The exact second-order remainder is conjugation by K. -/
theorem conjugationContinuous_secondOrder_remainder_eq_v007
    (U K : H →L[ℂ] H) :
    sandwichContinuous (U + K).adjoint (U + K) -
      (sandwichContinuous U.adjoint U +
        sandwichContinuous U.adjoint K +
        sandwichContinuous K.adjoint U) =
      sandwichContinuous K.adjoint K := by
  rw [conjugationContinuous_secondOrder_expand_v007]
  abel

/-- True Schatten S₁ operator-norm quadratic remainder bound:
the first-order (real-linear) term is bilaterally exact. -/
theorem conjugationContinuous_secondOrder_remainder_norm_le_v007
    (U K : H →L[ℂ] H) :
    ‖sandwichContinuous (U + K).adjoint (U + K) -
      (sandwichContinuous U.adjoint U +
        sandwichContinuous U.adjoint K +
        sandwichContinuous K.adjoint U)‖ ≤
      ‖K‖ ^ 2 := by
  rw [conjugationContinuous_secondOrder_remainder_eq_v007]
  calc
    ‖sandwichContinuous K.adjoint K‖ ≤
        ‖K.adjoint‖ * ‖K‖ := sandwichContinuous_norm_le _ _
    _ = ‖K‖ ^ 2 := by
      rw [← ContinuousLinearMap.star_eq_adjoint, norm_star]
      ring

#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_add_add_exact_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_secondOrder_expand_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_secondOrder_remainder_eq_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_secondOrder_remainder_norm_le_v007

end ProbabilisticTheory.TraceClass
