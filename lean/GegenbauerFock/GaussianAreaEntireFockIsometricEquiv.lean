import GegenbauerFock.GaussianAreaEntireDensityByMoments
import GegenbauerFock.GaussianAreaCoherentSeriesAe
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — surjective Gaussian Bargmann–Fock Hilbert isometry

The independent intrinsic Hilbert space consists of genuine Gaussian
L² classes admitting an everywhere complex-differentiable
representative. The monomial synthesis is an isometry into the ambient
planar L², and the preceding planar-moment uniqueness theorem identifies
its closed image with the entire-representative submodule.

The resulting map is a genuine surjective linear isometry, not merely
a sequence-space model or a formal Gram matrix. Compile and audit
against the pinned toolchain before reporting it as certified.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Extend the exact monomial synthesis to the intrinsically defined
holomorphic Gaussian L² Hilbert space. -/
noncomputable def coefficientSynthesisToIntrinsicEntireViaMoments
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  { toLinearMap :=
      (coefficientSynthesisL2 alpha ha).toLinearMap.codRestrict
        (entireGaussianL2Submodule alpha)
        (coefficientSynthesisL2_mem_entireGaussianL2Submodule alpha ha)
    norm_map' := by
      intro a
      change ‖coefficientSynthesisL2 alpha ha a‖ = ‖a‖
      exact (coefficientSynthesisL2 alpha ha).norm_map a }

/-- The Gaussian coefficient synthesis is onto the WHOLE independently
defined holomorphic Gaussian L² space, not just formal coefficients
or an unspecified closed polynomial subspace. -/
theorem coefficientSynthesisToIntrinsicEntireViaMoments_surjective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Surjective (coefficientSynthesisToIntrinsicEntireViaMoments alpha ha) := by
  intro y
  have hy :
      (y : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha := by
    rw [← intrinsicEntire_eq_gaussianPolynomialClosure alpha ha]
    exact y.property
  have hrange :
      (y : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact hy
  obtain ⟨a, hmem⟩ := hrange
  refine ⟨a, Subtype.ext ?_⟩
  exact hmem

/-- Full Gaussian Bargmann–Fock unitary Hilbert realization of all
square-summable normalized Taylor coefficients. -/
noncomputable def coefficientIntrinsicEntireEquivViaMoments
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  LinearIsometryEquiv.ofSurjective
    (coefficientSynthesisToIntrinsicEntireViaMoments alpha ha)
    (coefficientSynthesisToIntrinsicEntireViaMoments_surjective alpha ha)

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisToIntrinsicEntireViaMoments_surjective
#print axioms GegenbauerFock.GaussianArea.coefficientIntrinsicEntireEquivViaMoments

end GegenbauerFock.GaussianArea
