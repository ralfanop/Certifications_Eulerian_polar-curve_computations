import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramSpectral
import GegenbauerFock.GegenbauerIntrinsicEntireOutputGramZeroModes
import GegenbauerFock.TwoSidedGramProperDenseRange
import GegenbauerFock.TwoSidedGramContinuousSpectrum

/-!
# V007 — genuine intrinsic Bargmann–Fock output Gram range and spectral zero

The compact positive output Gram on the real Hilbert space of Gaussian
L² classes admitting entire representatives is injective but has dense,
proper, nonclosed image. Hence zero is in its continuous spectrum,
with no zero eigenvector and no surjectivity.

The unitary coefficient equivalence is used only to transfer failure
of surjectivity. Density comes independently from the Hilbert
adjoint/orthogonal-range theorem and already certified injectivity.
No finite-dimensional surrogate or claim that C_hol is onto is used.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual holomorphic Fock output Gram has dense image in the
full intrinsically defined complete entire Gaussian L² Hilbert space. -/
theorem C_intrinsicEntire_outputGram_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C_intrinsicEntire_outputGram lam alpha hlam ha).range.topologicalClosure =
      (⊤ : Submodule ℂ (GaussianArea.entireGaussianL2Submodule alpha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hker :
      (C_intrinsicEntire_outputGram lam alpha hlam ha).ker = ⊥ :=
    C_intrinsicEntire_outputGram_ker_bot lam alpha hlam ha
  apply (Submodule.topologicalClosure_eq_top_iff).2
  rw [(C_intrinsicEntire_outputGram lam alpha hlam ha).orthogonal_range,
      C_intrinsicEntire_outputGram_selfadjoint lam alpha hlam ha, hker]

/-- The compact true holomorphic output Gram is not onto the
entire Gaussian L² Hilbert space: its unitary conjugate C C† is not
surjective in the coefficient-space Hilbert model. -/
theorem C_intrinsicEntire_outputGram_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  intro hsurj
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  apply outputGram_not_surjective lam alpha hlam ha
  intro Fc
  obtain ⟨F, hF⟩ := hsurj (U Fc)
  refine ⟨U.symm F, ?_⟩
  have h := congrArg U.symm hF
  rw [C_intrinsicEntire_outputGram_apply] at h
  simpa only [U.symm_apply_apply] using h

/-- The actual dense range of the holomorphic output Gram is
nonclosed, and therefore cannot support bounded inversion. -/
theorem C_intrinsicEntire_outputGram_range_not_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ IsClosed ((C_intrinsicEntire_outputGram lam alpha hlam ha).range :
      Set (GaussianArea.entireGaussianL2Submodule alpha)) := by
  intro hclosed
  have htop :
      (C_intrinsicEntire_outputGram lam alpha hlam ha).range =
        (⊤ : Submodule ℂ (GaussianArea.entireGaussianL2Submodule alpha)) := by
    calc
      (C_intrinsicEntire_outputGram lam alpha hlam ha).range =
        (C_intrinsicEntire_outputGram lam alpha hlam ha).range.topologicalClosure :=
          (hclosed.submodule_topologicalClosure_eq).symm
      _ = ⊤ := C_intrinsicEntire_outputGram_dense_range lam alpha hlam ha
  exact C_intrinsicEntire_outputGram_not_surjective lam alpha hlam ha
    (LinearMap.range_eq_top.mp htop)

/-- Zero lies in the operator spectrum of the actual holomorphic
Gaussian output Gram, although its zero eigenspace is trivial. -/
theorem C_intrinsicEntire_outputGram_zero_mem_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (0 : ℂ) ∈ spectrum ℂ
      (C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  apply spectrum.zero_mem ℂ
  intro hunit
  exact C_intrinsicEntire_outputGram_not_surjective lam alpha hlam ha
    (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).2

/-- Zero is a point of continuous spectrum of the true analytic
output Gram: dense proper range, trivial kernel, spectral membership. -/
theorem C_intrinsicEntire_outputGram_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
       (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     IsContinuousSpectralPointAtZero
       (C_intrinsicEntire_outputGram lam alpha hlam ha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact ⟨C_intrinsicEntire_outputGram_zero_mem_spectrum lam alpha hlam ha,
    C_intrinsicEntire_outputGram_ker_bot lam alpha hlam ha,
    C_intrinsicEntire_outputGram_dense_range lam alpha hlam ha,
    C_intrinsicEntire_outputGram_not_surjective lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_not_surjective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_range_not_closed
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_zero_mem_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_zero_continuous_spectrum

end GegenbauerFock.GeneralUltrasphericalFock
