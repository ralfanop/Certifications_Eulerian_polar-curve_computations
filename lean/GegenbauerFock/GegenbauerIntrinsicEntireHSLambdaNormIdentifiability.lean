import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaStrictIdentifiability
import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer

/-!
# V007 — strict lambda order and identifiability from the HS norm itself

The previously certified strict antitonicity of the unregularized
Kummer mass also gives strict antitonicity of its square root.

Unlike the squared Hilbert–Schmidt energy, this is the actual
nonnegative basis-defined S2 norm of the Gaussian analytic-Fock
transform. Distinct ultraspherical source L2 spaces and unrelated
complete source Hilbert bases are explicitly allowed.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The square root of the exact Kummer mass is strictly antitone in
the positive ultraspherical parameter at fixed positive argument. -/
theorem kummerSeries_sqrt_strictAnti_lambda
    (lam₁ lam₂ z : ℝ)
    (hlam₁ : 0 < lam₁) (hlt : lam₁ < lam₂) (hz : 0 < z) :
    Real.sqrt (kummerSeries lam₂ z) <
      Real.sqrt (kummerSeries lam₁ z) := by
  have hlam₂ : 0 < lam₂ := lt_trans hlam₁ hlt
  have hnonneg : 0 ≤ kummerSeries lam₂ z := by
    have h := kummerSeries_ge_one lam₂ z hlam₂ hz.le
    linarith
  exact Real.sqrt_lt_sqrt hnonneg
    (kummerSeries_strictAnti_lambda lam₁ lam₂ z hlam₁ hlt hz)

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_sqrt_strictAnti_lambda

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Strict antitonicity of the actual basis-defined intrinsic
Gaussian-Fock Hilbert–Schmidt norm, not only of its square. -/
theorem C_intrinsicEntire_basisHSNorm_strictAnti_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlt : lam₁ < lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    Real.sqrt (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha (lt_trans hlam₁ hlt) ha (b₂ i)‖ ^ 2) <
    Real.sqrt (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam₂ alpha
        (lt_trans hlam₁ hlt) ha b₂,
      C_intrinsicEntire_basisHSNorm_eq_sqrt_kummer lam₁ alpha hlam₁ ha b₁]
  exact KummerCoefficients.kummerSeries_sqrt_strictAnti_lambda
    lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hlt (by positivity)

/-- Equality of the actual basis-defined intrinsic Gaussian-Fock
Hilbert–Schmidt norms identifies the positive source parameter
lambda, even with unrelated complete source bases. -/
theorem C_intrinsicEntire_basisHSNorm_identifies_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (heq :
      Real.sqrt (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) =
      Real.sqrt (∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha hlam₂ ha (b₂ i)‖ ^ 2)) :
    lam₁ = lam₂ := by
  rcases lt_trichotomy lam₁ lam₂ with hlt | hequal | hgt
  · have hstrict := C_intrinsicEntire_basisHSNorm_strictAnti_lambda
      lam₁ lam₂ alpha hlam₁ hlt ha b₁ b₂
    exact False.elim (hstrict.ne heq.symm)
  · exact hequal
  · have hstrict := C_intrinsicEntire_basisHSNorm_strictAnti_lambda
      lam₂ lam₁ alpha hlam₂ hgt ha b₂ b₁
    exact False.elim (hstrict.ne heq)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_strictAnti_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_basisHSNorm_identifies_lambda

end GegenbauerFock.GeneralUltrasphericalFock
