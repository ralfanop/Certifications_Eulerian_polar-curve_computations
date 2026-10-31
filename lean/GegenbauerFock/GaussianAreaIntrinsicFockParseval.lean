import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GaussianAreaCoefficientAnalysisAdjoint
import GegenbauerFock.GaussianAreaPolynomialProjector
import GegenbauerFock.GaussianAreaCoefficientSynthesisL2

/-!
# V007 — Parseval and Hilbert-series reconstruction for the full Fock space

The independently defined Gaussian entire L² Hilbert space has now been
proved equal to the closed normalized polynomial span. The exact
coefficient-analysis map therefore satisfies Parseval with no residual,
and its normalized monomial Fourier series converges in genuine
Gaussian L² norm for every intrinsic entire vector.

This is not a finite-rank or formal Gram-matrix identity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Every intrinsic Gaussian entire L² vector satisfies the full
Hilbert-space Parseval identity for normalized holomorphic monomials. -/
theorem intrinsicEntire_gaussian_parseval_norm
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ‖(x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ =
      ‖coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ := by
  obtain ⟨a, hax⟩ :=
    intrinsicEntire_exists_coefficient_synthesis alpha ha x
  rw [← hax, coefficientAnalysisL2_synthesis alpha ha a]
  exact coefficientSynthesisL2_norm alpha ha a

/-- The full Parseval identity also holds in the conventional
squared-norm form, with no positive residual term. -/
theorem intrinsicEntire_gaussian_parseval_sq
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ‖(x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ ^ 2 =
      ‖coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha))‖ ^ 2 := by
  rw [intrinsicEntire_gaussian_parseval_norm alpha ha x]

/-- The full Gaussian L² class equals the Hilbert-space limit of
its actual infinite normalized-holomorphic-monomial Fourier series. -/
theorem intrinsicEntire_gaussian_monomial_hasSum
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    HasSum (fun n : ℕ =>
      (coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n) •
          normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  have hx :
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) ∈
        gaussianPolynomialClosure alpha ha :=
    intrinsicEntire_le_polynomialClosure_unconditional alpha ha x.property
  have hfix :
      gaussianPolynomialProjector alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) :=
    (gaussianPolynomialProjector_eq_self_iff alpha ha _).2 hx
  have hs := coefficientSynthesisL2_hasSum alpha ha
    (coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)))
  change HasSum (fun n : ℕ =>
      (coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n) •
          normalizedMonomialL2Vector alpha ha n)
    (gaussianPolynomialProjector alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha))) at hs
  rw [hfix] at hs
  exact hs

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_gaussian_parseval_norm
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_gaussian_parseval_sq
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_gaussian_monomial_hasSum

end GegenbauerFock.GaussianArea
