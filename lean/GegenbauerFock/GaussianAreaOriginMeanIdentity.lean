import GegenbauerFock.GaussianAreaFullIntrinsicEvaluation
import GegenbauerFock.GaussianAreaEntireMomentInner
import GegenbauerFock.FockEvaluationSequence

/-!
# V007 — genuine Gaussian mean-value identity at the Bargmann–Fock vacuum

For a full intrinsically entire Gaussian L² representative, the value
at the origin equals the actual normalized two-dimensional Gaussian
area expectation of the function. This is the zeroth coefficient of
the previously certified surjective Hilbert coefficient analysis.

The integral is with respect to the genuine Gaussian-area measure;
no formal Fock expectation or polynomial-density premise is inserted.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The zeroth normalized holomorphic Gaussian monomial is constant one
for any real Gaussian parameter (normalization itself is independent
of the parameter at n=0). -/
theorem monomialWeight_zero (alpha : ℝ) :
    monomialWeight alpha 0 = 1 := by
  simp [monomialWeight]

/-- Actual two-dimensional Gaussian integration of any intrinsic
entire Gaussian L² representative reproduces its analytic value at
zero, without restricting to finite holomorphic polynomials. -/
theorem intrinsicEntire_origin_eq_gaussian_mean
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    intrinsicEntireEvaluation alpha ha 0 x =
      ∫ z : ℂ, entireRepresentative alpha x z
        ∂gaussianAreaMeasure alpha := by
  rw [intrinsicEntireEvaluation_eq_coherent_analysis alpha ha x 0]
  rw [FockEvaluation.evaluation_at_zero alpha ha]
  rw [coefficientAnalysisL2_apply alpha ha
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) 0]
  rw [normalizedMonomial_inner_entire_eq_moment alpha ha x 0]
  simp [monomialWeight_zero]

#print axioms GegenbauerFock.GaussianArea.monomialWeight_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_origin_eq_gaussian_mean

end GegenbauerFock.GaussianArea
