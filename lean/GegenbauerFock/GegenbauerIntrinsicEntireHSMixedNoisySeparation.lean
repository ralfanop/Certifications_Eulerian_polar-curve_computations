import GegenbauerFock.GegenbauerIntrinsicEntireHSMixedQuantitativeGap

/-!
# V007 — bounded observational error for coordinatewise-comparable pairs

Given two coordinatewise-ordered positive parameter pairs, and two
Kummer/Fock scalar masses fitting a shared observation within the
absolute errors eps₁ and eps₂, the sum of the two exact first-excited
parameter gaps is at most eps₁ + eps₂.

This is an effective, noise-stable *comparability-restricted* joint
separation theorem, not unrestricted recovery of two real parameters
from one scalar measurement.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The combined first-excited lambda and alpha separation of
ordered positive parameter pairs is controlled by their shared
observation error budgets. -/
theorem kummerSeries_mixed_noisy_gap
    (lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    (h₁ : |kummerSeries lam₁ (1 / (4 * alpha₁)) - y| ≤ eps₁)
    (h₂ : |kummerSeries lam₂ (1 / (4 * alpha₂)) - y| ≤ eps₂) :
    (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) +
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
    eps₁ + eps₂ := by
  have hgap := kummerSeries_mixed_quantitative_gap
    lam₁ lam₂ alpha₁ alpha₂ hlam₁ hleL ha₁ ha₂ hleA
  have hupper : kummerSeries lam₁ (1 / (4 * alpha₁)) - y ≤ eps₁ :=
    (abs_le.mp h₁).2
  have hlower : -eps₂ ≤
      kummerSeries lam₂ (1 / (4 * alpha₂)) - y :=
    (abs_le.mp h₂).1
  linarith

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_mixed_noisy_gap

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Combined lambda-alpha separation under errors in genuine
entire-Gaussian-Fock Hilbert–Schmidt squared energies, with arbitrary
complete source Hilbert bases on different source L² spaces. -/
theorem C_intrinsicEntire_HS_energy_mixed_noisy_gap
    (lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |(∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha₁ hlam₁ ha₁ (b₁ i)‖ ^ 2) - y| ≤ eps₁)
    (h₂ : |(∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂
          (b₂ i)‖ ^ 2) - y| ≤ eps₂) :
    (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) +
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
    eps₁ + eps₂ := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer
      lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_HS_energy_eq_kummer
      lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_noisy_gap
    lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂
    hlam₁ hleL ha₁ ha₂ hleA h₁ h₂

/-- Identical robust first-excited lambda-alpha gap for the real
diagonal traces of the genuine intrinsic source-Gram operators. -/
theorem C_intrinsicEntire_Gram_trace_mixed_noisy_gap
    (lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂ : ℝ)
    (hlam₁ : 0 < lam₁) (hleL : lam₁ ≤ lam₂)
    (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hleA : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (h₁ : |(∑' i : ι₁, RCLike.re (inner ℂ
       (C_intrinsicEntire_gram lam₁ alpha₁ hlam₁ ha₁ (b₁ i)) (b₁ i))) -
       y| ≤ eps₁)
    (h₂ : |(∑' i : ι₂, RCLike.re (inner ℂ
       (C_intrinsicEntire_gram lam₂ alpha₂
         (lt_of_lt_of_le hlam₁ hleL) ha₂ (b₂ i)) (b₂ i))) - y| ≤ eps₂) :
    (lam₂ - lam₁) / (8 * alpha₁ * (lam₁ + 1) * (lam₂ + 1)) +
      (alpha₂ - alpha₁) / (8 * (lam₂ + 1) * alpha₁ * alpha₂) ≤
    eps₁ + eps₂ := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₁ alpha₁ hlam₁ ha₁ b₁] at h₁
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer
      lam₂ alpha₂ (lt_of_lt_of_le hlam₁ hleL) ha₂ b₂] at h₂
  exact KummerCoefficients.kummerSeries_mixed_noisy_gap
    lam₁ lam₂ alpha₁ alpha₂ y eps₁ eps₂
    hlam₁ hleL ha₁ ha₂ hleA h₁ h₂

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_mixed_noisy_gap
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_mixed_noisy_gap

end GegenbauerFock.GeneralUltrasphericalFock
