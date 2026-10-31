import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedNoisySeparation

/-!
# V007 — separate quantitative recovery of two comparable parameters

Suppose 0 < lambda₁ ≤ lambda₂ ≤ L and
0 < alpha₁ ≤ alpha₂ ≤ A. If the two exact Fock scalar masses
are both within errors eps₁, eps₂ of the same observed y, then

  lambda₂-lambda₁ ≤ 8 A (L+1)^2 (eps₁+eps₂)
  alpha₂-alpha₁ ≤ 8 (L+1) A^2 (eps₁+eps₂).

Both bounds follow from the nonnegative first-excited coefficients
in the certified mixed parameter gap. They do NOT imply global joint
identifiability for noncomparable parameter pairs.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Separate error bounds for both positive parameters on an ordered
rectangle, from one common approximate Kummer mass measurement. -/
theorem kummerSeries_mixed_coordinate_noisy_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    (h₁ : |kummerSeries lam₁ (1 / (4 * alpha₁)) - y| ≤ eps₁)
    (h₂ : |kummerSeries lam₂ (1 / (4 * alpha₂)) - y| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 * (eps₁ + eps₂) := by
  have hdenL : 0 < 8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1) := by
    positivity
  have hdenA : 0 < 8 * (lam₂ + 1) * alpha₁ * alpha₂ := by
    positivity
  have hpartL :
      0 ≤ (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) :=
    div_nonneg (sub_nonneg.mpr hleL) hdenL.le
  have hpartA :
      0 ≤ (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) :=
    div_nonneg (sub_nonneg.mpr hleA) hdenA.le
  have hgap := kummerSeries_mixed_noisy_gap
    lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂
    hlam₁ hleL ha₁ ha₂ hleA h₁ h₂
  have hboundL :
      (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) ≤
        eps₁ + eps₂ := by linarith
  have hboundA :
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
        eps₁ + eps₂ := by linarith
  have herr : 0 ≤ eps₁ + eps₂ :=
    add_nonneg ((abs_nonneg _).trans h₁) ((abs_nonneg _).trans h₂)
  have hLpos : 0 < L + 1 := by linarith
  have hApos : 0 < A := lt_of_lt_of_le ha₂ hhiA
  have hdenLbound :
      8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1) ≤
        8 * A * (L + 1) ^ 2 := by
    calc
      8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1) ≤
          8 * A * (L + 1) * (L + 1) := by
        gcongr <;> linarith
      _ = 8 * A * (L + 1) ^ 2 := by ring
  have hdenAbound :
      8 * (lam₂ + 1) * alpha₁ * alpha₂ ≤
        8 * (L + 1) * A ^ 2 := by
    calc
      8 * (lam₂ + 1) * alpha₁ * alpha₂ ≤
          8 * (L + 1) * A * A := by
        gcongr <;> linarith
      _ = 8 * (L + 1) * A ^ 2 := by ring
  constructor
  · calc
      lam₂ - lam₁ ≤
          (eps₁ + eps₂) * (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) :=
        (div_le_iff₀ hdenL).mp hboundL
      _ ≤ (eps₁ + eps₂) * (8 * A * (L + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left hdenLbound herr
      _ = 8 * A * (L + 1) ^ 2 * (eps₁ + eps₂) := by ring
  · calc
      alpha₂ - alpha₁ ≤
          (eps₁ + eps₂) * (8 * (lam₂ + 1) * alpha₁ * alpha₂) :=
        (div_le_iff₀ hdenA).mp hboundA
      _ ≤ (eps₁ + eps₂) * (8 * (L + 1) * A ^ 2) :=
        mul_le_mul_of_nonneg_left hdenAbound herr
      _ = 8 * (L + 1) * A ^ 2 * (eps₁ + eps₂) := by ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_coordinate_noisy_recovery

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Separate lambda and Gaussian-width errors from actual intrinsic
entire-Fock squared S₂ energies on unrelated complete source bases,
for coordinatewise comparable parameter pairs. -/
theorem C_intrinsicEntire_HS_energy_mixed_coordinate_noisy_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |(∑' i : ι₁,
       ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |(∑' i : ι₂,
       ‖C_intrinsicEntire lam₂ alpha₂
         (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)‖ ^ 2) - y| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer
    lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_HS_energy_eq_kummer
    lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁ h₂

/-- Same separate parameter error control from actual intrinsic
source-Gram real diagonal traces with unrelated complete bases. -/
theorem C_intrinsicEntire_Gram_trace_mixed_coordinate_noisy_recovery
    (lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂) (hhiL : lam₂ ≤ L)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂) (hhiA : alpha₂ ≤ A)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |(∑' i : ι₁, RCLike.re (inner ℂ
       (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i)) (b₁ i))) - y|
         ≤ eps₁)
    (h₂ : |(∑' i : ι₂, RCLike.re (inner ℂ
       (C_intrinsicEntire_gram lam₂ alpha₂
         (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)) (b₂ i))) - y| ≤ eps₂) :
    lam₂ - lam₁ ≤ 8 * A * (L + 1) ^ 2 * (eps₁ + eps₂) ∧
    alpha₂ - alpha₁ ≤ 8 * (L + 1) * A ^ 2 * (eps₁ + eps₂) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
    lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
    lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_coordinate_noisy_recovery
    lam₁ lam₂ L alpha₁ alpha₂ A y eps₁ eps₂
    hlam₁ hleL hhiL ha₁ ha₂ hleA hhiA h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_mixed_coordinate_noisy_recovery
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_mixed_coordinate_noisy_recovery

end GegenbauerFock.GeneralUltrasphericalFock
