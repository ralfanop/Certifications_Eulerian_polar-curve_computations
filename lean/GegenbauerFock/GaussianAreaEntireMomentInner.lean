import GegenbauerFock.GaussianAreaEntireMomentIntegrability
import GegenbauerFock.GaussianAreaL2Orthonormality

/-!
# V007 — true Gaussian L² inner products are genuine entire moments

For an independently defined entire Gaussian L² class, the scalar
coefficient against the normalized holomorphic monomial is its actual
integral moment multiplied by the positive normalization weight.
There is no assumption of polynomial density or surjectivity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The Hilbert coefficient of an intrinsic entire Gaussian-L² class
equals the genuine normalized Gaussian-area integral of its entire
representative against the conjugate monomial. -/
theorem normalizedMonomial_inner_entire_eq_moment
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
    monomialWeight alpha n *
      (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
        ∂gaussianAreaMeasure alpha) := by
  calc
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
      (∫ z : ℂ, entireRepresentative alpha x z *
        star (normalizedMonomial alpha n z)
        ∂gaussianAreaMeasure alpha) := by
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards
            [normalizedMonomialL2Vector_ae alpha ha n,
             entireRepresentative_ae alpha x] with z hn hx
          rw [hn, ← hx]
          simp only [RCLike.inner_apply, starRingEnd_apply]
    _ = monomialWeight alpha n *
        (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
          ∂gaussianAreaMeasure alpha) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          simp only [normalizedMonomial, star_mul,
            star_monomialWeight]
          ring

#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_inner_entire_eq_moment

end GegenbauerFock.GaussianArea
