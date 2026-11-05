import GegenbauerFock.GegenbauerIntrinsicEntireHSAlphaQuantitative
import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- Sharp first-excited-coefficient lower separation in the physical
Gaussian width alpha, for fixed positive ultraspherical parameter. -/
theorem kummerSeries_alpha_first_gap
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hle : alpha₁ ≤ alpha₂) :
    (alpha₂ - alpha₁) / (8 * (lam + 1) * alpha₁ * alpha₂) ≤
      kummerSeries lam (1 / (4 * alpha₁)) -
        kummerSeries lam (1 / (4 * alpha₂)) := by
  have hd : lam + 1 ≠ 0 := ne_of_gt (by linarith)
  have ha₁' : alpha₁ ≠ 0 := ne_of_gt ha₁
  have ha₂' : alpha₂ ≠ 0 := ne_of_gt ha₂
  have hcoef :
      ratio lam 1 * (1 / (4 * alpha₁) - 1 / (4 * alpha₂)) =
        (alpha₂ - alpha₁) / (8 * (lam + 1) * alpha₁ * alpha₂) := by
    simp only [ratio_succ, ratio_zero, Nat.cast_zero, zero_add, one_mul]
    field_simp [hd, ha₁', ha₂']
    ring
  have hargs : (1 / (4 * alpha₂) : ℝ) ≤ 1 / (4 * alpha₁) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  calc
    (alpha₂ - alpha₁) / (8 * (lam + 1) * alpha₁ * alpha₂) =
        ratio lam 1 * (1 / (4 * alpha₁) - 1 / (4 * alpha₂)) :=
      hcoef.symm
    _ ≤ kummerSeries lam (1 / (4 * alpha₁)) -
          kummerSeries lam (1 / (4 * alpha₂)) :=
      kummerSeries_argument_first_gap
        lam (1 / (4 * alpha₂)) (1 / (4 * alpha₁))
        hlam (by positivity) hargs

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_alpha_first_gap

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Quantitative Gaussian-width separation by intrinsic entire-Fock
Hilbert–Schmidt squared energies, independent of the complete bases. -/
theorem C_intrinsicEntire_HS_energy_alpha_first_gap
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hle : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (alpha₂ - alpha₁) / (8 * (lam + 1) * alpha₁ * alpha₂) ≤
      (∑' i : ι₁, ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) -
      (∑' i : ι₂, ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam alpha₁ hlam ha₁ b₁,
      C_intrinsicEntire_HS_energy_eq_kummer lam alpha₂ hlam ha₂ b₂]
  exact KummerCoefficients.kummerSeries_alpha_first_gap
    lam alpha₁ alpha₂ hlam ha₁ ha₂ hle

/-- Exact Gaussian scale gap for the real diagonal traces of the
intrinsic source-Gram operators with arbitrary complete source bases. -/
theorem C_intrinsicEntire_Gram_trace_alpha_first_gap
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hle : alpha₁ ≤ alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (alpha₂ - alpha₁) / (8 * (lam + 1) * alpha₁ * alpha₂) ≤
      (∑' i : ι₁, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha₁ hlam ha₁ (b₁ i)) (b₁ i))) -
      (∑' i : ι₂, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam alpha₂ hlam ha₂ (b₂ i)) (b₂ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₁ hlam ha₁ b₁,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer lam alpha₂ hlam ha₂ b₂]
  exact KummerCoefficients.kummerSeries_alpha_first_gap
    lam alpha₁ alpha₂ hlam ha₁ ha₂ hle

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_alpha_first_gap
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_alpha_first_gap

end GegenbauerFock.GeneralUltrasphericalFock
