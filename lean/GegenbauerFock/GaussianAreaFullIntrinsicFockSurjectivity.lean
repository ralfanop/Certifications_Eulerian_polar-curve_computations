import GegenbauerFock.GaussianAreaPlanarMomentUniqueness
import GegenbauerFock.GaussianAreaEntireMomentPolarInner
import GegenbauerFock.GaussianAreaIntrinsicResidualCriterion
import GegenbauerFock.GaussianAreaPolynomialClosureEquiv

/-!
# V007 — full intrinsic Gaussian Bargmann–Fock isometric surjectivity

The Gaussian holomorphic polynomial span is all of the independently
defined intrinsic entire Gaussian L² submodule. The proof invokes
actual planar Gaussian moments, the Fubini/circle-average/Gamma/Taylor
uniqueness chain, and the previously certified Hilbert coefficient
analysis. No density premise and no analytic surjectivity assumption
is used.

This module is NOT a certificate until exact-commit Lean CI succeeds
and all individual axioms are independently checked.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Polynomial closure contains every intrinsic entire Gaussian L²
class because its orthogonal residual has all genuine planar
holomorphic moments zero and therefore vanishes identically. -/
theorem intrinsicEntire_le_polynomialClosure_unconditional
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha := by
  apply (intrinsicEntire_le_polynomialClosure_iff_moment_unique alpha ha).2
  intro x hx hcoeff
  let y : entireGaussianL2Submodule alpha := ⟨x, hx⟩
  have hplanar : ∀ n : ℕ,
      (∫ z : ℂ,
        ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
          (entireRepresentative alpha y z * star (z ^ n))) = 0 := by
    intro n
    have hcoef := hcoeff n
    have heq := normalizedMonomial_inner_eq_planar_entire_moment
      alpha ha y n
    rw [heq] at hcoef
    exact (mul_eq_zero.mp hcoef).resolve_left
      (monomialWeight_ne_zero alpha ha n)
  have hy : y = 0 :=
    intrinsicGaussian_zero_of_all_planar_moments_zero alpha ha y hplanar
  exact congrArg
    (fun v : entireGaussianL2Submodule alpha =>
      (v : Lp ℂ 2 (gaussianAreaMeasure alpha))) hy

/-- Every intrinsic entire Gaussian L² vector has an exact
square-summable coefficient synthesis, not only an approximation. -/
theorem intrinsicEntire_exists_coefficient_synthesis
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ∃ a : lp (fun _ : ℕ => ℂ) 2,
      coefficientSynthesisL2 alpha ha a =
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  have hx :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha :=
    intrinsicEntire_le_polynomialClosure_unconditional alpha ha x.property
  have hmem :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        LinearMap.range (coefficientSynthesisL2 alpha ha).toLinearMap := by
    rw [coefficientSynthesisL2_range_eq_closure_span alpha ha]
    exact hx
  exact hmem

/-- Actual Hilbert isometry into the independently defined entire
Gaussian subspace, before using the surjectivity theorem. -/
noncomputable def coefficientSynthesisToIntrinsicEntire
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 →ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  { toLinearMap :=
      (coefficientSynthesisL2 alpha ha).toLinearMap.codRestrict
        (entireGaussianL2Submodule alpha)
        (fun a =>
          gaussianPolynomialClosure_le_entireGaussianL2Submodule alpha ha
            (coefficientSynthesisL2_mem_gaussianPolynomialClosure alpha ha a))
    norm_map' := by
      intro a
      change ‖coefficientSynthesisL2 alpha ha a‖ = ‖a‖
      exact (coefficientSynthesisL2 alpha ha).norm_map a }

/-- The entire intrinsic Gaussian holomorphic L² submodule, not just
the polynomial closure, is the range of true Fock synthesis. -/
theorem coefficientSynthesisToIntrinsicEntire_surjective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Surjective (coefficientSynthesisToIntrinsicEntire alpha ha) := by
  intro x
  obtain ⟨a, ha'⟩ := intrinsicEntire_exists_coefficient_synthesis alpha ha x
  refine ⟨a, Subtype.ext ?_⟩
  exact ha'

/-- Exact surjective Hilbert isometry from square-summable
Bargmann–Fock coefficients onto all intrinsic entire Gaussian L²
classes, with no abstract replacement of the analytic function space. -/
noncomputable def coefficientIntrinsicEntireEquiv
    (alpha : ℝ) (ha : 0 < alpha) :
    lp (fun _ : ℕ => ℂ) 2 ≃ₗᵢ[ℂ] entireGaussianL2Submodule alpha :=
  LinearIsometryEquiv.ofSurjective
    (coefficientSynthesisToIntrinsicEntire alpha ha)
    (coefficientSynthesisToIntrinsicEntire_surjective alpha ha)

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_polynomialClosure_unconditional
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_exists_coefficient_synthesis
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisToIntrinsicEntire_surjective
#print axioms GegenbauerFock.GaussianArea.coefficientIntrinsicEntireEquiv

end GegenbauerFock.GaussianArea
