import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.TwoSidedGramInverseInstability

/-!
# V007 — quantitative inverse instability on the true analytic Fock output

The actual compact Gegenbauer output Gram on intrinsic holomorphic
Gaussian L² is unitarily conjugate to the coefficient-side Gram C C†.
The certified coefficient-side failure of every finite inverse stability
bound transfers without loss through the genuine onto Gaussian Fock
isometry. This theorem has a real analytic Gaussian L² output vector
as its witness, not merely an abstract sequence of Fock coefficients.

The true analytic output Gram remains injective; uniqueness is not
the same as stability of recovering an input from the Gram image.
-/

noncomputable section
open MeasureTheory
open scoped NNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- No finite uniform stability estimate for inversion of the actual
intrinsic Gaussian Fock output Gram on its dense nonclosed range. -/
theorem C_intrinsicEntire_outputGram_inverse_unbounded_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ F : GaussianArea.entireGaussianL2Submodule alpha,
      (K : ℝ) * ‖C_intrinsicEntire_outputGram lam alpha hlam ha F‖ < ‖F‖ := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  obtain ⟨Fc, hFc⟩ :=
    outputGram_inverse_unbounded_on_range lam alpha hlam ha K
  refine ⟨U Fc, ?_⟩
  rw [C_intrinsicEntire_outputGram_apply, U.symm_apply_apply]
  simpa only [U.norm_map] using hFc

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_inverse_unbounded_on_range

end GegenbauerFock.GeneralUltrasphericalFock
