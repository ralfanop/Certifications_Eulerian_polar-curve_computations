import GegenbauerFock.GaussianAreaProjectedPointEvaluation
import Mathlib.LinearAlgebra.Span.Basic

/-!
# V007 — intrinsic and projected evaluation agree on finite Gaussian polynomials

The intrinsic entire-representative evaluation and the bounded
coefficient-projection evaluation coincide on the *algebraic* complex
span of actual normalized Gaussian L² monomials. This is extended
from each monomial by complex linearity, not by assuming density.

The resulting coherent-state norm bound is proved for this finite
span only. Extension to all independently defined entire Gaussian
L² classes remains an analytic polynomial-density obligation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The finite complex-linear span of the genuine intrinsic Gaussian
holomorphic normalized monomials. -/
noncomputable def intrinsicGaussianPolynomialSpan
    (alpha : ℝ) (ha : 0 < alpha) :
    Submodule ℂ (entireGaussianL2Submodule alpha) :=
  Submodule.span ℂ (Set.range
    (fun n : ℕ => normalizedMonomialIntrinsicVector alpha ha n))

/-- On every finite holomorphic Gaussian polynomial, intrinsic
point evaluation agrees with the independently constructed bounded
ambient Gaussian L² projected evaluation. -/
theorem intrinsicEntireEvaluation_eq_projected_on_polynomialSpan
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : entireGaussianL2Submodule alpha)
    (hx : x ∈ intrinsicGaussianPolynomialSpan alpha ha) :
    intrinsicEntireEvaluation alpha ha z x =
      projectedGaussianEvaluation alpha ha z
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  have h :
      Set.EqOn
        (intrinsicEntireEvaluation alpha ha z)
        ((projectedGaussianEvaluation alpha ha z).toLinearMap.comp
          (entireGaussianL2Submodule alpha).subtype)
        (Set.range (fun n : ℕ =>
          normalizedMonomialIntrinsicVector alpha ha n)) := by
    rintro y ⟨n, rfl⟩
    exact (projectedGaussianEvaluation_normalizedMonomial alpha ha n z).symm
  exact LinearMap.eqOn_span h hx

/-- The true intrinsic analytic point evaluation satisfies the
coherent-state Gaussian L² bound on every finite polynomial. This
does not yet establish a bounded functional on the full intrinsic
holomorphic Gaussian L² space. -/
theorem intrinsicEntireEvaluation_norm_le_on_polynomialSpan
    (alpha : ℝ) (ha : 0 < alpha) (z : ℂ)
    (x : entireGaussianL2Submodule alpha)
    (hx : x ∈ intrinsicGaussianPolynomialSpan alpha ha) :
    ‖intrinsicEntireEvaluation alpha ha z x‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ * ‖x‖ := by
  rw [intrinsicEntireEvaluation_eq_projected_on_polynomialSpan
    alpha ha z x hx]
  exact projectedGaussianEvaluation_norm_le alpha ha z
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))

#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_eq_projected_on_polynomialSpan
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_norm_le_on_polynomialSpan

end GegenbauerFock.GaussianArea
