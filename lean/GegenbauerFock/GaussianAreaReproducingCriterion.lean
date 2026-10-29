import GegenbauerFock.GaussianAreaIntrinsicResidualCriterion

/-!
# V007 — intrinsic Gaussian reproducing formula as an exact onto criterion

This module does not assume polynomial density. It shows that an intrinsic
entire Gaussian L² class belongs to the genuine closed polynomial span
if and only if its *actual* entire point evaluation agrees everywhere
with the independently constructed bounded coherent-state evaluation
of its Gaussian coefficient sequence.

In particular, full surjectivity of the coefficient synthesis onto the
intrinsic entire Gaussian space is equivalent to the unconditional
Gaussian reproducing formula for all such classes. The latter remains
an analytic proof obligation; no conditional result is mislabelled
as a density or onto theorem.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- For a fixed intrinsic entire Gaussian L² vector, the coherent-state
reproducing formula at every complex point holds exactly when the vector
lies in the closed Gaussian holomorphic polynomial span. -/
theorem intrinsicEvaluation_eq_projected_iff_mem_polynomialClosure
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    (∀ z : ℂ, intrinsicEntireEvaluation alpha ha z x =
      projectedGaussianEvaluation alpha ha z
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) ↔
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha := by
  constructor
  · intro h
    let p : entireGaussianL2Submodule alpha :=
      ⟨gaussianPolynomialProjector alpha ha
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha)),
        gaussianPolynomialClosure_le_entireGaussianL2Submodule alpha ha
          (gaussianPolynomialProjector_mem_closure alpha ha
            (x : Lp ℂ 2 (gaussianAreaMeasure alpha)))⟩
    have hxp : x = p := by
      apply intrinsicEntireEvaluation_separates alpha ha
      intro z
      calc
        intrinsicEntireEvaluation alpha ha z x =
            projectedGaussianEvaluation alpha ha z
              (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := h z
        _ = projectedGaussianEvaluation alpha ha z
              (gaussianPolynomialProjector alpha ha
                (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) :=
          (projectedGaussianEvaluation_projector alpha ha z
            (x : Lp ℂ 2 (gaussianAreaMeasure alpha))).symm
        _ = intrinsicEntireEvaluation alpha ha z p :=
          (intrinsicEntireEvaluation_eq_projected_on_polynomialClosure
            alpha ha z
            (gaussianPolynomialProjector alpha ha
              (x : Lp ℂ 2 (gaussianAreaMeasure alpha)))
            (gaussianPolynomialProjector_mem_closure alpha ha
              (x : Lp ℂ 2 (gaussianAreaMeasure alpha)))).symm
    rw [hxp]
    exact gaussianPolynomialProjector_mem_closure alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha))
  · intro hx z
    exact intrinsicEntireEvaluation_eq_projected_on_polynomialClosure
      alpha ha z (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) hx

/-- The entire intrinsic Gaussian space is exhausted by polynomial
synthesis if and only if every intrinsic entire Gaussian L² function
satisfies the exact coherent-state reproducing identity. -/
theorem intrinsicEntire_le_polynomialClosure_iff_reproducing
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≤ gaussianPolynomialClosure alpha ha ↔
      ∀ x : entireGaussianL2Submodule alpha, ∀ z : ℂ,
        intrinsicEntireEvaluation alpha ha z x =
          projectedGaussianEvaluation alpha ha z
            (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  constructor
  · intro h x
    exact (intrinsicEvaluation_eq_projected_iff_mem_polynomialClosure
      alpha ha x).2 (h x.property)
  · intro h x hx
    exact (intrinsicEvaluation_eq_projected_iff_mem_polynomialClosure
      alpha ha (⟨x, hx⟩ : entireGaussianL2Submodule alpha)).1
        (h ⟨x, hx⟩)

#print axioms GegenbauerFock.GaussianArea.intrinsicEvaluation_eq_projected_iff_mem_polynomialClosure
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_le_polynomialClosure_iff_reproducing

end GegenbauerFock.GaussianArea
