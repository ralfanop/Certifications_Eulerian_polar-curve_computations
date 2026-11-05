import GegenbauerFock.GaussianAreaIntrinsicRieszKernel
import GegenbauerFock.GaussianAreaIntrinsicPointwiseExpansion

/-!
# V007 — exact off-diagonal Riesz kernel as a convergent coherent series

Unlike an abstract reproducing-kernel identity, this theorem links the
true entire Gaussian-L² representative of the Riesz vector to the
actual convergent ℓ² inner-product series built from normalized Gaussian
monomial coordinates. It holds at all pairs of complex points.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The genuine intrinsic Gaussian Fock Riesz kernel is the coherent
ℓ² coordinate pairing of the evaluation vectors at any z,w∈ℂ. -/
theorem intrinsicRieszKernel_offDiagonal_tsum
    (alpha : ℝ) (ha : 0 < alpha) (z w : ℂ) :
    entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z =
      ∑' n : ℕ,
        inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
          (FockEvaluation.kernelCoordinate alpha w n) := by
  calc
    entireRepresentative alpha (intrinsicRieszKernel alpha ha w) z =
      intrinsicEntireEvaluationContinuous alpha ha z
        (coefficientSynthesisToIntrinsicEntire alpha ha
          (FockEvaluation.kernelVector alpha ha w)) := by
            rw [intrinsicEntireEvaluationContinuous_apply]
            rfl
    _ = FockEvaluation.evaluation alpha ha z
          (FockEvaluation.kernelVector alpha ha w) :=
        intrinsicEntireEvaluationContinuous_synthesis alpha ha z
          (FockEvaluation.kernelVector alpha ha w)
    _ = ∑' n : ℕ,
          inner ℂ (FockEvaluation.kernelCoordinate alpha z n)
            (FockEvaluation.kernelCoordinate alpha w n) :=
        FockEvaluation.evaluation_eq_tsum_inner alpha ha z
          (FockEvaluation.kernelVector alpha ha w)

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_offDiagonal_tsum

end GegenbauerFock.GaussianArea
