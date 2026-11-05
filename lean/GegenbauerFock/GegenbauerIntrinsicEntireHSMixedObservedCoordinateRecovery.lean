import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedNormCoordinateRecovery

/-!
# Observation-dependent joint parameter stability in Gaussian-Fock transforms

A fixed observation y of the *unsquared* intrinsic Gaussian-Fock S₂ norm
provides bounds on both coordinates of comparable parameter pairs, without
a uniform positive lower bound on the Gaussian width.

For 0 < lambda₁ ≤ lambda₂ ≤ L and 0 < alpha₁ ≤ alpha₂ ≤ A,
define the data-dependent error amplification
  δ = (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂).
Then
  lambda₂ - lambda₁ ≤ 8 A (L+1)^2 δ
  alpha₂ - alpha₁ ≤ 8 (L+1) A^2 δ.

These are comparability-restricted conclusions. In particular they do not
assert that a single scalar observation identifies two unrestricted parameters.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Absolute errors in two unsquared positive Kummer masses around a
common real observation imply a bound on the difference of their squares,
with an amplification factor computed exclusively from observed data. -/
theorem kummerSeries_mixed_observed_energy_gap
    (lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    kummerSeries lam₁ (1 / (4 * alpha₁)) -
      kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
    (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
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
  have he : 0 ≤ eps₁ + eps₂ := add_nonneg he₁ he₂
  have hu₁ : Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y ≤ eps₁ :=
    (abs_le.mp h₁).2
  have hu₂ : Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y ≤ eps₂ :=
    (abs_le.mp h₂).2
  have hy : y ≤ |y| := le_abs_self y
  have hsum :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤
      2 * |y| + eps₁ + eps₂ := by linarith
  have hsum_nn :
      0 ≤ Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) := by positivity
  have htri :
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤
      eps₁ + eps₂ := by
    calc
      |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| ≤
        |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| +
        |y - Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))| :=
          abs_sub_le _ _ _
      _ = |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| +
          |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y| := by
        rw [abs_sub_comm y
          (Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))))]
      _ ≤ eps₁ + eps₂ := add_le_add h₁ h₂
  have hdiff :
      Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) -
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) ≤ eps₁ + eps₂ :=
    (le_abs_self _).trans htri
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
    _ ≤ (eps₁ + eps₂) *
      (Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) +
        Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂)))) :=
      mul_le_mul_of_nonneg_right hdiff hsum_nn
    _ ≤ (eps₁ + eps₂) * (2 * |y| + eps₁ + eps₂) :=
      mul_le_mul_of_nonneg_left hsum he
    _ = (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by ring

/-- Quantitative recovery of both coordinates from a noisy *unsquared*
Kummer mass on a bounded, ordered parameter rectangle, without any
uniform strictly positive lower bound on alpha. -/
theorem kummerSeries_mixed_observed_coordinate_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    (h₁ : |Real.sqrt (kummerSeries lam₁ (1 / (4 * alpha₁))) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (kummerSeries lam₂ (1 / (4 * alpha₂))) - y| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hleL
  have horder :
      kummerSeries lam₂ (1 / (4 * alpha₂)) ≤
        kummerSeries lam₁ (1 / (4 * alpha₁)) :=
    kummerSeries_mixed_antitone
      lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA
  have hgap := kummerSeries_mixed_observed_energy_gap
    lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂
    hlam₁ hlam₂ ha₁ ha₂ h₁ h₂
  have hfit₁ :
      |kummerSeries lam₁ (1 / (4 * alpha₁)) -
        kummerSeries lam₂ (1 / (4 * alpha₂))| ≤
      (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
    rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    exact hgap
  have hfit₂ :
      |kummerSeries lam₂ (1 / (4 * alpha₂)) -
        kummerSeries lam₂ (1 / (4 * alpha₂))| ≤ (0 : ℝ) := by simp
  have hresult := kummerSeries_mixed_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A
    (kummerSeries lam₂ (1 / (4 * alpha₂)))
    ((2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂)) 0
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA hfit₁ hfit₂
  constructor
  · calc
      lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        ((2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) + 0) := hresult.1
      _ = 8 * A * (L + 1) ^ 2 *
          (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by ring
  · calc
      alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        ((2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) + 0) := hresult.2
      _ = 8 * (L + 1) * A ^ 2 *
          (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_observed_energy_gap
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_observed_coordinate_recovery

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Data-adaptive joint recovery of comparable ultraspherical and
Gaussian parameters from true basis-defined Fock Hilbert–Schmidt
norm measurements, with independent complete source Hilbert bases. -/
theorem C_intrinsicEntire_basisHSNorm_mixed_observed_coordinate_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |Real.sqrt (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |Real.sqrt (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)‖ ^ 2) - y|
      ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 *
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 *
        (2 * |y| + eps₁ + eps₂) * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer
    lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_observed_coordinate_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_mixed_observed_coordinate_recovery

end GegenbauerFock.GeneralUltrasphericalFock
