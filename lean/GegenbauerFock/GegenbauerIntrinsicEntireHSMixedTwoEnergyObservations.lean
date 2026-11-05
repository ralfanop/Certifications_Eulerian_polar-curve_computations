import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedCoordinateRecovery

/-!
# Two-observation stability for actual Gaussian-Fock Hilbert–Schmidt energies

For two coordinatewise-ordered positive pairs
0 < lambda₁ ≤ lambda₂ ≤ L and 0 < alpha₁ ≤ alpha₂ ≤ A,
observed squared Hilbert–Schmidt masses y₁, y₂ with errors eps₁, eps₂
give both parameter error bounds with a common observable quantity

  delta = |y₁-y₂| + eps₁ + eps₂.

The same result applies to intrinsic source-Gram real diagonal traces.
No positive lower bound on alpha is needed because the observations
concern squared S₂ energies, not unsquared S₂ norms.

The coordinatewise comparability hypothesis cannot be dropped:
a single scalar energy does not globally identify two parameters.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Distinct noisy observations of Kummer energies quantitatively
control both positive ordered parameters, using only the absolute
observation discrepancy and the two certified error budgets. -/
theorem kummerSeries_mixed_two_energy_observations
    (lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    (h₁ : |kummerSeries lam₁ (1 / (4 * alpha₁)) - y₁| ≤ eps₁)
    (h₂ : |kummerSeries lam₂ (1 / (4 * alpha₂)) - y₂| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        (|y₁ - y₂| + eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        (|y₁ - y₂| + eps₁ + eps₂) := by
  have h₁' :
      |kummerSeries lam₁ (1 / (4 * alpha₁)) - y₂| ≤
        |y₁ - y₂| + eps₁ := by
    calc
      |kummerSeries lam₁ (1 / (4 * alpha₁)) - y₂| ≤
          |kummerSeries lam₁ (1 / (4 * alpha₁)) - y₁| +
            |y₁ - y₂| := abs_sub_le _ _ _
      _ ≤ |y₁ - y₂| + eps₁ := by linarith
  have hbase := kummerSeries_mixed_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A y₂
    (|y₁ - y₂| + eps₁) eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁' h₂
  constructor
  · calc
      lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
          ((|y₁ - y₂| + eps₁) + eps₂) := hbase.1
      _ = 8 * A * (L + 1) ^ 2 *
          (|y₁ - y₂| + eps₁ + eps₂) := by ring
  · calc
      alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
          ((|y₁ - y₂| + eps₁) + eps₂) := hbase.2
      _ = 8 * (L + 1) * A ^ 2 *
          (|y₁ - y₂| + eps₁ + eps₂) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_two_energy_observations

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Stable recovery from two distinct noisy measurements of the
genuine Hilbert–Schmidt squared energies of intrinsic entire-Fock
operators on different ultraspherical source L² spaces. -/
theorem C_intrinsicEntire_HS_energy_mixed_two_observations
    (lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |(∑' i : ι₁,
       ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) - y₁| ≤ eps₁)
    (h₂ : |(∑' i : ι₂,
       ‖C_intrinsicEntire lam₂ alpha₂
         (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)‖ ^ 2) - y₂| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        (|y₁ - y₂| + eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        (|y₁ - y₂| + eps₁ + eps₂) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer
      lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_HS_energy_eq_kummer
      lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_two_energy_observations
    lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁ h₂

/-- Same separate parameter recovery estimates from two distinct
observations of source-Gram real diagonal traces for unrelated
complete source Hilbert bases. -/
theorem C_intrinsicEntire_Gram_trace_mixed_two_observations
    (lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |(∑' i : ι₁, RCLike.re (inner ℂ
       (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i)) (b₁ i))) -
       y₁| ≤ eps₁)
    (h₂ : |(∑' i : ι₂, RCLike.re (inner ℂ
       (C_intrinsicEntire_gram lam₂ alpha₂
         (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)) (b₂ i))) - y₂| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        (|y₁ - y₂| + eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        (|y₁ - y₂| + eps₁ + eps₂) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_two_energy_observations
    lam₁ lam₂ L alpha₁ alpha₂ A y₁ y₂ eps₁ eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_mixed_two_observations
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_mixed_two_observations

end GegenbauerFock.GeneralUltrasphericalFock
