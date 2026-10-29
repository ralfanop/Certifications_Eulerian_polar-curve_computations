import GegenbauerFock.GaussianAreaMomentTaylorNormalized
import GegenbauerFock.GaussianAreaHilbertCoefficientsTaylor
import GegenbauerFock.GaussianAreaIntrinsicFockParseval
import GegenbauerFock.GaussianAreaEntireMomentPolarInner

/-!
# V007 — actual Fock Hilbert coefficients and norm-convergent Taylor–Fourier series

The fully normalized planar Gaussian moment computes every genuine
Hilbert-adjoint coefficient of an intrinsic entire Gaussian L² vector.
Substitution into the already certified unconditional monomial-series
reconstruction gives the corresponding explicitly weighted Taylor
expansion converging in the true Gaussian Hilbert norm.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Each actual Gaussian L² coefficient is the normalized monomial
weight times the exact alpha⁻ⁿ-scaled complex Taylor derivative. -/
theorem coefficientAnalysisL2_intrinsic_eq_scaled_taylor
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n =
      monomialWeight alpha n *
        (((alpha ^ (-(n : ℝ)) : ℝ) : ℂ) *
          iteratedDeriv n (entireRepresentative alpha x) 0) := by
  rw [coefficientAnalysisL2_apply alpha ha
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n]
  rw [normalizedMonomial_inner_eq_planar_entire_moment alpha ha x n]
  rw [intrinsicEntire_planar_gaussian_moment_eq_scaled_derivative alpha ha x n]

/-- The complete holomorphic Gaussian L² vector is the true Hilbert
norm limit of the monomial Fourier series with explicit Taylor-derivative
coefficients, without a polynomial density assumption. -/
theorem intrinsicEntire_scaledTaylor_monomial_hasSum
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    HasSum (fun n : ℕ =>
      (monomialWeight alpha n *
        (((alpha ^ (-(n : ℝ)) : ℝ) : ℂ) *
          iteratedDeriv n (entireRepresentative alpha x) 0)) •
          normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  simpa only [coefficientAnalysisL2_intrinsic_eq_scaled_taylor alpha ha x] using
    (intrinsicEntire_gaussian_monomial_hasSum alpha ha x)

#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_intrinsic_eq_scaled_taylor
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_scaledTaylor_monomial_hasSum

end GegenbauerFock.GaussianArea
