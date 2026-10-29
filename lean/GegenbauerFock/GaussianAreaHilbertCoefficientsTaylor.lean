import GegenbauerFock.GaussianAreaAllMomentsTaylorFormula
import GegenbauerFock.GaussianAreaEntireMomentInner
import GegenbauerFock.GaussianAreaCoefficientAnalysisAdjoint

/-!
# V007 — actual Hilbert-adjoint Fock coefficients as Gaussian Taylor data

We combine the genuine planar Gaussian n-th moment formula with the
normalization of the actual L² holomorphic monomial and the ambient
Hilbert adjoint of coefficient synthesis. These are not formal
coefficient functionals: they are computed from the real Gaussian
area measure on ℂ.

No additional polynomial-density or surjectivity assumption is used.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The n-th true Gaussian L² Hilbert coefficient of an independently
specified entire Gaussian L² class is its n-th Taylor derivative with
the exact (unreduced) factorial/Gamma normalization. -/
theorem coefficientAnalysisL2_intrinsic_eq_taylor_gamma
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n =
      monomialWeight alpha n *
        (((2 * alpha : ℝ) : ℂ) *
          (((alpha ^ (-((n : ℝ) + 1)) * (1 / 2) *
              (Nat.factorial n : ℝ) : ℝ) : ℂ) *
            (iteratedDeriv n (entireRepresentative alpha x) 0 /
              (Nat.factorial n : ℂ)))) := by
  rw [coefficientAnalysisL2_apply alpha ha
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n]
  rw [normalizedMonomial_inner_eq_planar_entire_moment alpha ha x n]
  rw [intrinsicEntire_planar_gaussian_moment_eq_taylor alpha ha x n]

/-- A genuine Gaussian L² Fock coefficient vanishes if and only if the
corresponding Taylor derivative of its entire representative vanishes.
The equivalence is individual for every n, not only simultaneous
vanishing of the whole coefficient sequence. -/
theorem coefficientAnalysisL2_intrinsic_zero_iff_taylor_deriv_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n = 0 ↔
      iteratedDeriv n (entireRepresentative alpha x) 0 = 0 := by
  rw [coefficientAnalysisL2_apply alpha ha
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) n]
  rw [normalizedMonomial_inner_eq_planar_entire_moment alpha ha x n]
  constructor
  · intro hz
    have hm :
        (∫ z : ℂ,
          ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
            (entireRepresentative alpha x z * star (z ^ n))) = 0 :=
      (mul_eq_zero.mp hz).resolve_left
        (monomialWeight_ne_zero alpha ha n)
    exact (intrinsicEntire_planar_moment_zero_iff_taylor_deriv_zero
      alpha ha x n).1 hm
  · intro hd
    have hm :
        (∫ z : ℂ,
          ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
            (entireRepresentative alpha x z * star (z ^ n))) = 0 :=
      (intrinsicEntire_planar_moment_zero_iff_taylor_deriv_zero
        alpha ha x n).2 hd
    rw [hm, mul_zero]

#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_intrinsic_eq_taylor_gamma
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_intrinsic_zero_iff_taylor_deriv_zero

end GegenbauerFock.GaussianArea
