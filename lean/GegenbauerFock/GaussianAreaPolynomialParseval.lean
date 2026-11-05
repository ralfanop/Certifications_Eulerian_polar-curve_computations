import GegenbauerFock.GaussianAreaPolynomialProjector

/-!
# V007 — Gaussian polynomial Parseval decomposition and Bessel bound

The true Gaussian L² polynomial projector P = S S† has an orthogonal
residual. Consequently the full ambient norm decomposes into the
squared ℓ² coefficient norm plus the squared residual norm. This is
the precise Parseval identity WITH a remainder; omitting the remainder
for arbitrary entire L² classes would be the still-unproved density
statement. In particular, coefficient analysis is contractive.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Orthogonal Pythagoras for the actual Gaussian L² polynomial
projection, including the genuinely orthogonal residual. -/
theorem gaussianPolynomialProjector_pythagoras
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    ‖x‖ ^ 2 =
      ‖gaussianPolynomialProjector alpha ha x‖ ^ 2 +
      ‖x - gaussianPolynomialProjector alpha ha x‖ ^ 2 := by
  have hinner :
      inner ℂ (gaussianPolynomialProjector alpha ha x)
        (x - gaussianPolynomialProjector alpha ha x) = 0 :=
    Submodule.inner_right_of_mem_orthogonal
      (gaussianPolynomialProjector_mem_closure alpha ha x)
      (gaussianPolynomialProjector_residual_orthogonal alpha ha x)
  have hsum :
      gaussianPolynomialProjector alpha ha x +
        (x - gaussianPolynomialProjector alpha ha x) = x := by
    abel
  calc
    ‖x‖ ^ 2 =
      ‖gaussianPolynomialProjector alpha ha x +
        (x - gaussianPolynomialProjector alpha ha x)‖ ^ 2 := by rw [hsum]
    _ = ‖gaussianPolynomialProjector alpha ha x‖ ^ 2 +
        ‖x - gaussianPolynomialProjector alpha ha x‖ ^ 2 :=
      (by simpa only [pow_two] using
        norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hinner)

/-- The concrete Gaussian polynomial projection is norm-contracting
on the whole weighted L² space. -/
theorem gaussianPolynomialProjector_norm_le
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    ‖gaussianPolynomialProjector alpha ha x‖ ≤ ‖x‖ := by
  have hp := gaussianPolynomialProjector_pythagoras alpha ha x
  have hsq :
      ‖gaussianPolynomialProjector alpha ha x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖x - gaussianPolynomialProjector alpha ha x‖]
  by_contra hn
  have hlt : ‖x‖ < ‖gaussianPolynomialProjector alpha ha x‖ :=
    lt_of_not_ge hn
  have hmul :
      0 < (‖gaussianPolynomialProjector alpha ha x‖ - ‖x‖) *
        (‖gaussianPolynomialProjector alpha ha x‖ + ‖x‖) := by
    apply mul_pos
    · linarith
    · linarith [norm_nonneg x]
  nlinarith

/-- Exact Parseval identity with the residual: the coefficient norm
alone equals the ambient norm iff the residual vanishes. -/
theorem gaussianCoefficientAnalysis_parseval_with_residual
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    ‖x‖ ^ 2 =
      ‖coefficientAnalysisL2 alpha ha x‖ ^ 2 +
      ‖x - gaussianPolynomialProjector alpha ha x‖ ^ 2 := by
  calc
    ‖x‖ ^ 2 =
      ‖gaussianPolynomialProjector alpha ha x‖ ^ 2 +
        ‖x - gaussianPolynomialProjector alpha ha x‖ ^ 2 :=
      gaussianPolynomialProjector_pythagoras alpha ha x
    _ = ‖coefficientAnalysisL2 alpha ha x‖ ^ 2 +
        ‖x - gaussianPolynomialProjector alpha ha x‖ ^ 2 := by
      rw [show ‖gaussianPolynomialProjector alpha ha x‖ =
          ‖coefficientAnalysisL2 alpha ha x‖ from
        (coefficientSynthesisL2 alpha ha).norm_map
          (coefficientAnalysisL2 alpha ha x)]

/-- Bessel inequality for the entire sequence of actual Gaussian
holomorphic monomial coefficients of an arbitrary weighted L² class. -/
theorem coefficientAnalysisL2_norm_le
    (alpha : ℝ) (ha : 0 < alpha)
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :
    ‖coefficientAnalysisL2 alpha ha x‖ ≤ ‖x‖ := by
  calc
    ‖coefficientAnalysisL2 alpha ha x‖ =
      ‖coefficientSynthesisL2 alpha ha
        (coefficientAnalysisL2 alpha ha x)‖ :=
      ((coefficientSynthesisL2 alpha ha).norm_map
        (coefficientAnalysisL2 alpha ha x)).symm
    _ = ‖gaussianPolynomialProjector alpha ha x‖ := rfl
    _ ≤ ‖x‖ := gaussianPolynomialProjector_norm_le alpha ha x

#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_pythagoras
#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_norm_le
#print axioms GegenbauerFock.GaussianArea.gaussianCoefficientAnalysis_parseval_with_residual
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_norm_le

end GegenbauerFock.GaussianArea
