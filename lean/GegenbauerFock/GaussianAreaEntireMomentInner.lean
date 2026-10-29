import GegenbauerFock.GaussianAreaEntireMomentIntegrability
import GegenbauerFock.GaussianAreaL2Orthonormality
import GegenbauerFock.GaussianAreaCoefficientAnalysisAdjoint

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


/-- The normalization of a true Gaussian monomial is nonzero for alpha>0. -/
theorem monomialWeight_ne_zero
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    monomialWeight alpha n ≠ 0 := by
  have hratio : 0 < alpha ^ n / (Nat.factorial n : ℝ) := by
    positivity
  have hroot : Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 hratio).ne'
  change ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ)) ≠ 0
  exact_mod_cast hroot

/-- Vanishing of a true L² Gaussian coefficient is equivalent to
vanishing of its actual complex integral moment. -/
theorem normalizedMonomial_inner_eq_zero_iff_entire_moment_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    inner ℂ (normalizedMonomialL2Vector alpha ha n)
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0 ↔
      (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
        ∂gaussianAreaMeasure alpha) = 0 := by
  rw [normalizedMonomial_inner_entire_eq_moment alpha ha x n]
  constructor
  · intro hz
    exact (mul_eq_zero.mp hz).resolve_left (monomialWeight_ne_zero alpha ha n)
  · intro hz
    apply mul_eq_zero.mpr
    exact Or.inr (by simpa only [star_pow] using hz)

/-- Intrinsic polynomial coefficient analysis vanishes precisely when
every genuine Gaussian integral moment of the chosen entire function
vanishes. This statement is independent of polynomial density. -/
theorem coefficientAnalysisL2_eq_zero_iff_entire_moments_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    coefficientAnalysisL2 alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) = 0 ↔
    ∀ n : ℕ,
      (∫ z : ℂ, entireRepresentative alpha x z * star (z ^ n)
        ∂gaussianAreaMeasure alpha) = 0 := by
  rw [coefficientAnalysisL2_eq_zero_iff alpha ha
    (x : Lp ℂ 2 (gaussianAreaMeasure alpha))]
  exact forall_congr' (fun n =>
    normalizedMonomial_inner_eq_zero_iff_entire_moment_zero alpha ha x n)

#print axioms GegenbauerFock.GaussianArea.monomialWeight_ne_zero
#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_inner_eq_zero_iff_entire_moment_zero
#print axioms GegenbauerFock.GaussianArea.coefficientAnalysisL2_eq_zero_iff_entire_moments_zero

#print axioms GegenbauerFock.GaussianArea.normalizedMonomial_inner_entire_eq_moment

end GegenbauerFock.GaussianArea
