import GegenbauerFock.GaussianAreaPolynomialOrthogonalCriterion
import GegenbauerFock.GaussianAreaCoefficientRecovery
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — ambient Gaussian L² coefficient analysis as a true Hilbert adjoint

The adjoint of the isometric coefficient synthesis exists on ALL of
Gaussian weighted L², not only on the closed holomorphic polynomial span.
It recovers coefficients on the synthesis range, computes each coefficient
as the actual Gaussian L² inner product with a normalized monomial, and
has precisely the orthogonal complement of the polynomial closure as kernel.

This is a basis-free Hilbert-space reduction of the remaining analytic
Bargmann–Fock onto/density problem; no onto theorem for the independently
defined entire-representative submodule is asserted here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Actual Hilbert adjoint of the Gaussian coefficient synthesis, defined
on the whole Gaussian L² space and taking values in square-summable sequences. -/
noncomputable def coefficientAnalysisL2
    (alpha : ℝ) (ha : 0 < alpha) :
    Lp ℂ 2 (gaussianAreaMeasure alpha) →L[ℂ]
      lp (fun _ : ℕ => ℂ) 2 :=
  (coefficientSynthesisL2 alpha ha).toContinuousLinearMap.adjoint

/-- Analysis is a left inverse of synthesis on all square-summable
coefficients; the identity follows from the adjoint of an isometry. -/
theorem coefficientAnalysisL2_synthesis
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    coefficientAnalysisL2 alpha ha (coefficientSynthesisL2 alpha ha a) = a := by
  have h := (coefficientSynthesisL2 alpha ha).adjoint_comp_self
  have h' := congrArg
    (fun T : lp (fun _ : ℕ => ℂ) 2 →L[ℂ]
      lp (fun _ : ℕ => ℂ) 2 => T a) h
  simpa [coefficientAnalysisL2] using h'

/-- The n-th analysis coefficient of ANY Gaussian L² vector is exactly
its Hilbert inner product against the normalized holomorphic monomial. -/
theorem coefficientAnalysisL2_apply
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) (n : ℕ) :
    coefficientAnalysisL2 alpha ha x n =
      inner ℂ (normalizedMonomialL2Vector alpha ha n) x := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (coefficientSynthesisL2 alpha ha).toContinuousLinearMap
    (lp.single 2 n (1 : ℂ)) x
  rw [show
      (coefficientSynthesisL2 alpha ha).toContinuousLinearMap
        (lp.single 2 n (1 : ℂ)) =
          normalizedMonomialL2Vector alpha ha n from
        coefficientSynthesisL2_single alpha ha n] at h
  change inner ℂ (lp.single 2 n (1 : ℂ))
    (coefficientAnalysisL2 alpha ha x) =
      inner ℂ (normalizedMonomialL2Vector alpha ha n) x at h
  rw [lp.inner_single_left] at h
  simpa using h

/-- The adjoint analysis kills exactly those ambient Gaussian L² vectors
whose complete family of holomorphic monomial moments vanishes. -/
theorem coefficientAnalysisL2_eq_zero_iff
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    coefficientAnalysisL2 alpha ha x = 0 ↔
      ∀ n : ℕ, inner ℂ (normalizedMonomialL2Vector alpha ha n) x = 0 := by
  constructor
  · intro hx n
    rw [← coefficientAnalysisL2_apply alpha ha x n, hx]
    rfl
  · intro hx
    apply lp.ext
    funext n
    rw [coefficientAnalysisL2_apply alpha ha x n]
    exact hx n

/-- Exact ambient L² kernel criterion: coefficient analysis vanishes
precisely on the orthogonal complement of the closed polynomial span. -/
theorem coefficientAnalysisL2_eq_zero_iff_orthogonal
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    coefficientAnalysisL2 alpha ha x = 0 ↔
      x ∈ (gaussianPolynomialClosure alpha ha)ᗮ := by
  rw [coefficientAnalysisL2_eq_zero_iff alpha ha x]
  exact (mem_gaussianPolynomialClosure_orthogonal_iff alpha ha x).symm

#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_synthesis
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_apply
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_eq_zero_iff
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_eq_zero_iff_orthogonal

end GegenbauerFock.GaussianArea
