import GegenbauerFock.GaussianAreaEntireMomentInner
import GegenbauerFock.GaussianAreaCoefficientAnalysisAdjoint

/-!
# V007 — exact kernel of intrinsic Gaussian moment analysis

The genuine normalized Gaussian-area moments of an independently
specified entire L² representative determine exactly the kernel
of the full Hilbert adjoint of coefficient synthesis.

This is a non-conditional equivalence of two actual integrals/maps,
but it does not by itself show that this kernel contains only zero.
The latter analytic uniqueness theorem is the remaining density task.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The adjoint coefficient analysis of a genuinely entire Gaussian
L² class is zero precisely when every one of its actual Gaussian-area
integral moments against a conjugate monomial is zero. -/
theorem intrinsicAnalysis_zero_iff_all_integral_moments_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0 ↔
      ∀ n : ℕ,
        (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
          ∂gaussianAreaMeasure alpha) = 0 := by
  rw [coefficientAnalysisL2_eq_zero_iff alpha ha
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))]
  constructor
  · intro hx n
    have hn := hx n
    rw [normalizedMonomial_inner_entire_eq_moment alpha ha x n] at hn
    exact (mul_eq_zero.mp hn).resolve_left
      (monomialWeight_ne_zero alpha ha n)
  · intro hx n
    rw [normalizedMonomial_inner_entire_eq_moment alpha ha x n,
      hx n, mul_zero]

#print axioms GegenbauerFock.GaussianArea.monomialWeight_ne_zero
#print axioms GegenbauerFock.GaussianArea.intrinsicAnalysis_zero_iff_all_integral_moments_zero

end GegenbauerFock.GaussianArea
