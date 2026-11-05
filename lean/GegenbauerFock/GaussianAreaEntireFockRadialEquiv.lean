import GegenbauerFock.GaussianAreaEntireRadialCoefficientDensity
import GegenbauerFock.GaussianAreaCoherentSeriesAe
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — intrinsic Gaussian Bargmann–Fock isometry via radial coefficients

This is the full Hilbert-space endpoint of the independent radial
coefficient uniqueness argument, avoiding the alternate planar
moment-normalization proof. The target is the genuine submodule of
weighted complex L² classes admitting an entire representative,
rather than a formal coefficient subspace.

A new source and its dependencies require exact-head CI and an
axiom audit before this result is called a Lean certificate.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Genuine L² normalized-monomial synthesis with intrinsic entire
Gaussian L² codomain, preserving the full infinite coefficient norm. -/
noncomputable def coefficientSynthesisToIntrinsicViaRadial
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

/-- The normalized Gaussian monomials span the entire independently
specified holomorphic Gaussian L² space, with no density hypothesis. -/
theorem coefficientSynthesisToIntrinsicViaRadial_surjective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Surjective (coefficientSynthesisToIntrinsicViaRadial alpha ha) := by
  intro y
  have hy :
      (y : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha := by
    rw [← intrinsicEntire_eq_polynomialClosure_via_radial_inner alpha ha]
    exact y.property
  have hrange :
      (y : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact hy
  obtain ⟨a, ha⟩ := hrange
  refine ⟨a, Subtype.ext ?_⟩
  exact ha

/-- Full linear isometric equivalence between ℓ² Gaussian Taylor
coefficients and every intrinsic entire Gaussian L² class. -/
noncomputable def coefficientIntrinsicEntireEquivViaRadial
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  LinearIsometryEquiv.ofSurjective
    (coefficientSynthesisToIntrinsicViaRadial alpha ha)
    (coefficientSynthesisToIntrinsicViaRadial_surjective alpha ha)

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisToIntrinsicViaRadial_surjective
#print axioms GegenbauerFock.GaussianArea.coefficientIntrinsicEntireEquivViaRadial

end GegenbauerFock.GaussianArea
