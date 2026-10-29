import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.OutputGramSpectrum

/-!
# V007 — exact output Gram Hilbert pairing and positivity in genuine Fock L²

The true Gegenbauer-to-entire-Fock map has an actual Hilbert adjoint,
and its output Gram acts on Gaussian L² classes with entire representatives.
Using the surjective Bargmann–Fock unitary, its pairings are those of
the independently defined coefficient-side output Gram C C†.
In particular the real quadratic form is nonnegative.

No new spectral assumption is introduced, and no false surjectivity of
the compact ultraspherical transform is asserted.
-/

noncomputable section
open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact preservation of complex Hilbert pairings for the genuine
intrinsic entire Gaussian Fock output Gram. -/
theorem C_intrinsicEntire_outputGram_inner_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F G : GaussianArea.entireGaussianL2Submodule alpha) :
    inner ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha F) G =
      inner ℂ
        (outputGram lam alpha hlam ha
          ((GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).symm F))
        ((GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).symm G) := by
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  rw [C_intrinsicEntire_outputGram_apply]
  have h := U.inner_map_map
    (outputGram lam alpha hlam ha (U.symm F)) (U.symm G)
  simpa only [U.apply_symm_apply] using h

/-- A genuine nonnegative quadratic form for the analytic Gaussian
Fock output Gram, in the intrinsic complete holomorphic subspace. -/
theorem C_intrinsicEntire_outputGram_re_inner_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : GaussianArea.entireGaussianL2Submodule alpha) :
    0 ≤ RCLike.re
      (inner ℂ (C_intrinsicEntire_outputGram lam alpha hlam ha F) F) := by
  rw [C_intrinsicEntire_outputGram_inner_eq]
  have hadj :
      (C_adjoint lam alpha hlam ha).adjoint =
        C lam alpha hlam ha := by
    unfold C_adjoint
    simp
  have hgram :
      outputGram lam alpha hlam ha =
        HilbertGram.gram (C_adjoint lam alpha hlam ha) := by
    change (C lam alpha hlam ha).comp (C_adjoint lam alpha hlam ha) =
      (C_adjoint lam alpha hlam ha).adjoint ∘L
        (C_adjoint lam alpha hlam ha)
    rw [hadj]
    rfl
  rw [hgram]
  exact HilbertGram.gram_re_nonneg (C_adjoint lam alpha hlam ha)
    ((GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).symm F)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_inner_eq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_re_inner_nonneg

end GegenbauerFock.GeneralUltrasphericalFock
