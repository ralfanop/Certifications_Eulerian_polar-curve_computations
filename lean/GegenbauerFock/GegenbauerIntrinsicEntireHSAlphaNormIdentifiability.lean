import GegenbauerFock.GegenbauerIntrinsicEntireHSScaleIdentifiability
import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaNormIdentifiability

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The square root of the positive Kummer mass strictly decreases
with increasing positive Gaussian scale alpha at fixed lambda. -/
theorem kummerSeries_sqrt_strictAnti_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hlt : alpha₁ < alpha₂) :
    Real.sqrt (kummerSeries lam (1 / (4 * alpha₂))) <
      Real.sqrt (kummerSeries lam (1 / (4 * alpha₁))) := by
  have hscale : (4 * alpha₁ : ℝ) < 4 * alpha₂ := by nlinarith
  have hargs : (1 / (4 * alpha₂) : ℝ) < 1 / (4 * alpha₁) :=
    one_div_lt_one_div_of_lt (by positivity) hscale
  have hnonneg : 0 ≤ kummerSeries lam (1 / (4 * alpha₂)) := by
    have h := kummerSeries_ge_one lam (1 / (4 * alpha₂))
      hlam (by positivity)
    linarith
  exact Real.sqrt_lt_sqrt hnonneg
    (kummerSeries_strictMono_nonneg lam
      (1 / (4 * alpha₂)) (1 / (4 * alpha₁))
      hlam (by positivity) hargs)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_sqrt_strictAnti_alpha

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual intrinsic entire-Fock Hilbert–Schmidt norm is
strictly decreasing as the Gaussian width alpha increases. -/
theorem C_intrinsicEntire_basisHSNorm_strictAnti_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    (hlt : alpha₁ < alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Real.sqrt (∑' i : ι₂,
      ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2) <
    Real.sqrt (∑' i : ι₁,
      ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam alpha₂ hlam ha₂ b₂,
      C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam alpha₁ hlam ha₁ b₁]
  exact KummerCoefficients.kummerSeries_sqrt_strictAnti_alpha
    lam alpha₁ alpha₂ hlam ha₁ ha₂ hlt

/-- Equality of actual intrinsic Gaussian Fock S2 norms forces
equal positive Gaussian widths, independently of the source basis. -/
theorem C_intrinsicEntire_basisHSNorm_identifies_alpha
    (lam alpha₁ alpha₂ : ℝ)
    (hlam : 0 < lam) (ha₁ : 0 < alpha₁) (ha₂ : 0 < alpha₂)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
    (heq :
      Real.sqrt (∑' i : ι₁,
        ‖C_intrinsicEntire lam alpha₁ hlam ha₁ (b₁ i)‖ ^ 2) =
      Real.sqrt (∑' i : ι₂,
        ‖C_intrinsicEntire lam alpha₂ hlam ha₂ (b₂ i)‖ ^ 2)) :
    alpha₁ = alpha₂ := by
  rcases lt_trichotomy alpha₁ alpha₂ with hlt | hequal | hgt
  · have hs := C_intrinsicEntire_basisHSNorm_strictAnti_alpha
      lam alpha₁ alpha₂ hlam ha₁ ha₂ hlt b₁ b₂
    exact False.elim (hs.ne heq.symm)
  · exact hequal
  · have hs := C_intrinsicEntire_basisHSNorm_strictAnti_alpha
      lam alpha₂ alpha₁ hlam ha₂ ha₁ hgt b₂ b₁
    exact False.elim (hs.ne heq)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_strictAnti_alpha
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_identifies_alpha

end GegenbauerFock.GeneralUltrasphericalFock
