import GegenbauerFock.GeneralUltrasphericalFock
import GegenbauerFock.OperatorExpBound

/-!
# V007: quantitative operator-norm theorem for the actual ultraspherical Fock map

C_{λ,α}: L²(ν_λ) → ℓ² is the specifically constructed, bounded,
compact coefficient operator, with λ>0 and α>0.

This bound is for the entire infinite-dimensional operator:
  ‖C_{λ,α}‖ <= sqrt(exp(1/(4α))).
It does not require a finite cutoff or a new hypothesis on C.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem C_opNorm_le_exp (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) :
    ‖C lam alpha hlam ha‖ ≤
      Real.sqrt (Real.exp (1 / (4 * alpha))) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  change ‖ConcreteFock.operator (Ultraspherical.measure lam)
    (ae_abs_le_one lam) alpha ha‖ ≤
    Real.sqrt (Real.exp (1 / (4 * alpha)))
  exact ConcreteFock.operator_norm_le_sqrt_exp
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_opNorm_le_exp

end GegenbauerFock.GeneralUltrasphericalFock
