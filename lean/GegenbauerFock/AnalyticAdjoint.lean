import GegenbauerFock.EvaluationComposite
import GegenbauerFock.AdjointBasis

/-!
# V007: analytic Gegenbauer–Fock adjoint on coherent vectors and all coefficients

We identify the genuine Hilbert adjoint on every coherent reproducing
vector, and provide a norm-convergent L² expansion of its action on
an arbitrary Fock coefficient vector.  The equivalence of this L²
expansion with pointwise evaluation of the reconstructed entire
function is an additional, explicitly separate theorem.
-/

open MeasureTheory
open scoped ENNReal InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The adjoint of coherent Fock point evaluation takes the scalar
one to the coherent kernel vector in genuine ℓ². -/
theorem fockEvaluation_adjoint_one
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    (FockEvaluation.evaluation alpha ha z).adjoint (1 : ℂ) =
      FockEvaluation.kernelVector alpha ha z := by
  change ((innerSL ℂ) (FockEvaluation.kernelVector alpha ha z)).adjoint 1 =
      FockEvaluation.kernelVector alpha ha z
  rw [ContinuousLinearMap.adjoint_innerSL_apply]
  simp

/-- Exact coherent-state restriction of the actual Hilbert adjoint
for every complex z and all positive Gegenbauer–Fock parameters.
The right-hand side is a genuine L² class with pointwise representative
u ↦ exp(-i * conjugate(z) * u / 2). -/
theorem C_adjoint_coherent
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) (z : ℂ) :
    C_adjoint lam alpha hlam ha
      (FockEvaluation.kernelVector alpha ha z) =
        Ultraspherical.originalCoherentLp lam hlam (-star z) := by
  calc
    C_adjoint lam alpha hlam ha
        (FockEvaluation.kernelVector alpha ha z) =
      (evaluatedOperator lam alpha hlam ha z).adjoint (1 : ℂ) := by
        rw [evaluatedOperator_adjoint_apply,
          fockEvaluation_adjoint_one alpha ha z]
        rfl
    _ = Ultraspherical.originalCoherentLp lam hlam (-star z) := by
      rw [evaluatedOperator_adjoint_coherent]
      simp

/-- For arbitrary infinite Fock coefficients, the Hilbert adjoint
is the norm-convergent sum in L² of its actual weighted moment-row
adjoints.  This is an identity for the entire operator, not merely
for finite truncations. -/
theorem C_adjoint_eq_tsum_rows
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    C_adjoint lam alpha hlam ha F =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ,
        (WeightedMoments.coefficient
          (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n).adjoint
            (F n) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  have hs : HasSum (fun n : ℕ => lp.single 2 n (F n)) F :=
    lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) F
  have hm := (C_adjoint lam alpha hlam ha).hasSum hs
  calc
    C_adjoint lam alpha hlam ha F =
        ∑' n : ℕ,
          C_adjoint lam alpha hlam ha (lp.single 2 n (F n)) :=
            hm.tsum_eq.symm
    _ = ∑' n : ℕ,
          (WeightedMoments.coefficient
            (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n).adjoint
              (F n) := by
        apply tsum_congr
        intro n
        change (ConcreteFock.operator
          (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha).adjoint
            (lp.single 2 n (F n)) = _
        exact FockAdjointBasis.adjoint_single
          (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha ha n (F n)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.fockEvaluation_adjoint_one
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_coherent
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_eq_tsum_rows

end GegenbauerFock.GeneralUltrasphericalFock
