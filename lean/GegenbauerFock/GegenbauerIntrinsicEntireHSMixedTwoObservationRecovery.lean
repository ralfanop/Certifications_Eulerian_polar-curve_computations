import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedCoordinateRecovery
import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedParameterOrder

/-!
# Stable reconstruction from two distinct Gaussian-Fock measurements

For comparable ordered positive parameter pairs, two different
observations y₁ and y₂ of the unsquared Fock Hilbert–Schmidt norms
give explicit error bounds on both parameter coordinates, without
a Gaussian-width lower bound.

Write δ = (|y₁|+|y₂|+eps₁+eps₂) * (|y₁-y₂|+eps₁+eps₂).
When 0 < lambda₁ ≤ lambda₂ ≤ L and 0 < alpha₁ ≤ alpha₂ ≤ A,
we establish
  lambda₂-lambda₁ ≤ 8*A*(L+1)^2*δ
  alpha₂-alpha₁ ≤ 8*(L+1)*A^2*δ.

The constraint of coordinatewise comparability is essential to the claim.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Stability of exact squared Kummer masses under two *different*
noisy observations of their square roots. The bound involves only
the reported observations and error budgets. -/
theorem kummerSeries_mixed_two_observation_energy_gap
    (lam₁ lam₂ alpha₁ alpha₂ y₁ y₂ eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y₁| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y₂| ≤ eps₂) :
    kummerSeries lam₁ (1 / (4 * alpha₁)) -
      kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
    (|y₁| + |y₂| + eps₁ + eps₂) *
      (|y₁ - y₂| + eps₁ + eps₂) := by
  have hK₁ : 0 ≤ kummerSeries lam₁ (1 / (4 * alpha₁)) := by
    have h := kummerSeries_ge_one lam₁ (1 / (4 * alpha₁))
      hlam₁ (by positivity)
    linarith
  have hK₂ : 0 ≤ kummerSeries lam₂ (1 / (4 * alpha₂)) := by
    have h := kummerSeries_ge_one lam₂ (1 / (4 * alpha₂))
      hlam₂ (by positivity)
    linarith
  have he₁ : 0 ≤ eps₁ := (abs_nonneg _).trans h₁
  have he₂ : 0 ≤ eps₂ := (abs_nonneg _).trans h₂
  have hderr : 0 ≤ |y₁ - y₂| + eps₁ + eps₂ := by positivity
  have hy₁ : y₁ ≤ |y₁| := le_abs_self y₁
  have hy₂ : y₂ ≤ |y₂| := le_abs_self y₂
  have hu₁ : Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y₁ ≤ eps₁ :=
    (abs_le.mp h₁).2
  have hu₂ : Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y₂ ≤ eps₂ :=
    (abs_le.mp h₂).2
  have hsum :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤
      |y₁| + |y₂| + eps₁ + eps₂ := by linarith
  have hsum_nn :
      0 ≤ Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) := by positivity
  have ht₁ :
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y₁| +
        |y₁ - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| :=
    abs_sub_le _ _ _
  have ht₂ :
      |y₁ - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤
      |y₁ - y₂| + |y₂ - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| :=
    abs_sub_le _ _ _
  have ht₃ :
      |y₂ - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤ eps₂ := by
    rw [abs_sub_comm]
    exact h₂
  have hdiff :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤
        |y₁ - y₂| + eps₁ + eps₂ := by
    have habs := le_abs_self
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
       Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))))
    linarith
  have hfactor :
      kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂)) =
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) := by
    nlinarith [Real.sq_sqrt hK₁, Real.sq_sqrt hK₂]
  calc
    kummerSeries lam₁ (1 / (4 * alpha₁)) -
      kummerSeries lam₂ (1 / (4 * alpha₂)) =
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) := hfactor
    _ ≤ (|y₁ - y₂| + eps₁ + eps₂) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) :=
      mul_le_mul_of_nonneg_right hdiff hsum_nn
    _ ≤ (|y₁ - y₂| + eps₁ + eps₂) *
        (|y₁| + |y₂| + eps₁ + eps₂) :=
      mul_le_mul_of_nonneg_left hsum hderr
    _ = (|y₁| + |y₂| + eps₁ + eps₂) *
        (|y₁ - y₂| + eps₁ + eps₂) := by ring

/-- Data-dependent coordinatewise inverse estimates from two
independent noisy Hilbert–Schmidt norm measurements of comparable
positive Gaussian-Fock parameter pairs. -/
theorem kummerSeries_mixed_two_observation_coordinate_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y₁| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y₂| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
      ((|y₁| + |y₂| + eps₁ + eps₂) *
        (|y₁ - y₂| + eps₁ + eps₂)) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
      ((|y₁| + |y₂| + eps₁ + eps₂) *
        (|y₁ - y₂| + eps₁ + eps₂)) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  have horder :
      kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
        kummerSeries lam₁ (1 / (4 * alpha₁)) :=
    kummerSeries_mixed_antitone
      lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA
  have hgap := kummerSeries_mixed_two_observation_energy_gap
    lam₁ lam₂ alpha₁ alpha₂ y₁ y₂ eps₁ eps₂
    hlam₁ hlam₂ ha₁ ha₂ h₁ h₂
  have hfit₁ :
      |kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂))| ≤
      (|y₁| + |y₂| + eps₁ + eps₂) *
        (|y₁ - y₂| + eps₁ + eps₂) := by
    rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact hgap
  have hfit₂ :
      |kummerSeries lam₂ (1 / (4 * alpha₂)) -
        kummerSeries lam₂ (1 / (4 * alpha₂))| ≤ (0 : ℝ) := by simp
  have hresult := kummerSeries_mixed_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A
    (kummerSeries lam₂ (1 / (4 * alpha₂)))
    ((|y₁| + |y₂| + eps₁ + eps₂) *
      (|y₁ - y₂| + eps₁ + eps₂)) 0
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA hfit₁ hfit₂
  constructor
  · calc
      lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        ((|y₁| + |y₂| + eps₁ + eps₂) *
          (|y₁ - y₂| + eps₁ + eps₂) + 0) := hresult.1
      _ = 8 * A * (L + 1) ^ 2 *
        ((|y₁| + |y₂| + eps₁ + eps₂) *
          (|y₁ - y₂| + eps₁ + eps₂)) := by ring
  · calc
      alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        ((|y₁| + |y₂| + eps₁ + eps₂) *
          (|y₁ - y₂| + eps₁ + eps₂) + 0) := hresult.2
      _ = 8 * (L + 1) * A ^ 2 *
        ((|y₁| + |y₂| + eps₁ + eps₂) *
          (|y₁ - y₂| + eps₁ + eps₂)) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_two_observation_energy_gap
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_two_observation_coordinate_recovery

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Quantitative reconstruction from two distinct observed Fock S₂ norms
on positive coordinatewise-comparable parameter pairs with unrelated
complete Hilbert bases in their respective ultraspherical source spaces. -/
theorem C_intrinsicEntire_basisHSNorm_mixed_two_observation_coordinate_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |Real.sqrt (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) - y₁| ≤ eps₁)
    (h₂ : |Real.sqrt (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)‖ ^ 2) - y₂|
      ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
      ((|y₁| + |y₂| + eps₁ + eps₂) *
        (|y₁ - y₂| + eps₁ + eps₂)) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
      ((|y₁| + |y₂| + eps₁ + eps₂) *
        (|y₁ - y₂| + eps₁ + eps₂)) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_two_observation_coordinate_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_mixed_two_observation_coordinate_recovery

end GegenbauerFock.GeneralUltrasphericalFock
