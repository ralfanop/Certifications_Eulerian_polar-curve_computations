import GegenbauerFock.GaussianAreaIntrinsicEvaluationSharpNorm
import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.FockEvaluationSequence

/-!
# V007 — actual Riesz reproducing vectors in intrinsic Gaussian Bargmann–Fock

The Riesz kernel is synthesized into the independently defined
holomorphic Gaussian-L² Hilbert submodule from the genuine ℓ² coherent
kernel vector. This proves reproducing via the actual intrinsic inner
product, not merely coefficient pairing or formal polynomial kernels.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The Gaussian coherent kernel is a genuine intrinsic holomorphic
Gaussian-L² class, constructed by isometric coefficient synthesis. -/
noncomputable def intrinsicRieszKernel
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    entireGaussianL2Submodule alpha :=
  coefficientSynthesisToIntrinsicEntire alpha ha
    (FockEvaluation.kernelVector alpha ha z)

/-- Every intrinsic entire Gaussian-L² function reproduces from the
actual Hilbert inner product with the coherent Gaussian kernel. -/
theorem intrinsicRieszKernel_inner
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : entireGaussianL2Submodule alpha) :
    inner ℂ (intrinsicRieszKernel alpha ha z) x =
      entireRepresentative alpha x z := by
  obtain ⟨a, rfl⟩ :=
    coefficientSynthesisToIntrinsicEntire_surjective alpha ha x
  calc
    inner ℂ (intrinsicRieszKernel alpha ha z)
        (coefficientSynthesisToIntrinsicEntire alpha ha a) =
      inner ℂ (FockEvaluation.kernelVector alpha ha z) a :=
        (coefficientSynthesisToIntrinsicEntire alpha ha).inner_map_map _ _
    _ = FockEvaluation.evaluation alpha ha z a := rfl
    _ = intrinsicEntireEvaluationContinuous alpha ha z
        (coefficientSynthesisToIntrinsicEntire alpha ha a) :=
          (intrinsicEntireEvaluationContinuous_synthesis alpha ha z a).symm
    _ = entireRepresentative alpha
        (coefficientSynthesisToIntrinsicEntire alpha ha a) z := by
          rw [intrinsicEntireEvaluationContinuous_apply]
          rfl

/-- The coherent reproducing vector has exactly the ℓ² kernel norm,
not only an upper bound, in the actual intrinsic Gaussian L² space. -/
theorem intrinsicRieszKernel_norm
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖intrinsicRieszKernel alpha ha z‖ =
      ‖FockEvaluation.kernelVector alpha ha z‖ := by
  exact (coefficientSynthesisToIntrinsicEntire alpha ha).norm_map _

/-- The full intrinsic kernel has sharp diagonal Gaussian norm. -/
theorem intrinsicRieszKernel_norm_sq
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖intrinsicRieszKernel alpha ha z‖ ^ 2 =
      Real.exp (alpha * ‖z‖ ^ 2) := by
  rw [intrinsicRieszKernel_norm]
  exact FockEvaluation.kernelVector_norm_sq alpha ha z

#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_inner
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_norm
#print axioms GegenbauerFock.GaussianArea.intrinsicRieszKernel_norm_sq

end GegenbauerFock.GaussianArea
