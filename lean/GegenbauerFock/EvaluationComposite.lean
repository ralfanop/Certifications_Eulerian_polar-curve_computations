import GegenbauerFock.FockEvaluationSequence
import GegenbauerFock.GeneralUltrasphericalFock

/-!
# V007: Fock point evaluation of the concrete ultraspherical Hilbert operator

This theorem combines the bounded evaluation functional on the
coefficient Hilbert space with the concrete ultraspherical Fock
operator and proves an exact, convergent coefficient-series formula
for their composition.

The final identification of this series with the Bochner Fourier
integral ∫ f(u) exp(i z u / 2) dν_λ(u) is a separate convergence and
term-by-term-integration theorem, not smuggled into this declaration.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem evaluation_C_eq_tsum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (z : ℂ) (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    FockEvaluation.evaluation alpha ha z (C lam alpha hlam ha f) =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ, inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
        (WeightedMoments.coefficient (Ultraspherical.measure lam)
          (ae_abs_le_one lam) alpha n f) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [FockEvaluation.evaluation_eq_tsum_inner]
  apply tsum_congr
  intro n
  rw [C_coefficient lam alpha hlam ha f n]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.evaluation_C_eq_tsum

end GegenbauerFock.GeneralUltrasphericalFock
