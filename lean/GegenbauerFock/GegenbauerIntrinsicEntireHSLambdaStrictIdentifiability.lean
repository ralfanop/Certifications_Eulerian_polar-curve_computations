import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaOrder
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# V007 — strict ultraspherical parameter ordering and identifiability

For 0 < λ₁ < λ₂ and every positive Kummer argument, the first
nonvacuum coefficient decreases strictly while all other coefficients
decrease weakly. Hence the exact full intrinsic Gaussian-Fock S₂ mass
and source-Gram diagonal trace are strictly antitone in λ.

The two source Hilbert spaces need not coincide. The statements compare
only scalar invariants and allow two unrelated complete source bases.
No operator order between different source spaces is asserted.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The first excited Pochhammer coefficient strictly decreases in λ. -/
theorem ratio_strictAnti_lambda_one
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 < lam₁) (hlt : lam₁ < lam₂) :
    ratio lam₂ 1 < ratio lam₁ 1 := by
  simp only [ratio_succ, ratio_zero, Nat.cast_zero, zero_add, one_mul]
  have hd₁ : 0 < lam₁ + 1 := by linarith
  have hd₂ : 0 < lam₂ + 1 := by linarith
  apply (div_lt_div_iff₀ hd₂ hd₁).2
  nlinarith

/-- Strict antitonicity of the exact unregularized real Kummer series
for positive argument, witnessed by the coefficient with n=1. -/
theorem kummerSeries_strictAnti_lambda
    (lam₁ lam₂ z : ℝ) (hlam₁ : 0 < lam₁)
    (hlt : lam₁ < lam₂) (hz : 0 < z) :
    kummerSeries lam₂ z < kummerSeries lam₁ z := by
  have hlam₂ : 0 < lam₂ := lt_trans hlam₁ hlt
  have hnonneg (n : ℕ) :
      0 ≤ ratio lam₂ n * (z ^ n / (Nat.factorial n : ℝ)) :=
    mul_nonneg (ratio_nonneg lam₂ hlam₂ n) (by positivity)
  have hterms (n : ℕ) :
      ratio lam₂ n * (z ^ n / (Nat.factorial n : ℝ)) ≤
      ratio lam₁ n * (z ^ n / (Nat.factorial n : ℝ)) :=
    mul_le_mul_of_nonneg_right
      (ratio_antitone_lambda lam₁ lam₂ hlam₁ hlt.le n) (by positivity)
  have hfirst :
      ratio lam₂ 1 * (z ^ 1 / (Nat.factorial 1 : ℝ)) <
      ratio lam₁ 1 * (z ^ 1 / (Nat.factorial 1 : ℝ)) := by
    simpa using (mul_lt_mul_of_pos_right
      (ratio_strictAnti_lambda_one lam₁ lam₂ hlam₁ hlt) hz)
  unfold kummerSeries
  exact Summable.tsum_lt_tsum_of_nonneg (i := 1)
    hnonneg hterms hfirst (kummerSeries_summable lam₁ z hlam₁ hz.le)

#print axioms GegenbauerFock.KummerCoefficients.ratio_strictAnti_lambda_one
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_strictAnti_lambda

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual analytic Gaussian-Fock Hilbert–Schmidt energy decreases
strictly with the positive ultraspherical λ at fixed positive α. -/
theorem C_intrinsicEntire_HS_energy_strictAnti_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlt : lam₁ < lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha (lt_trans hlam₁ hlt) ha (b₂ i)‖ ^ 2) <
    (∑' i : ι₁,
      ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₂ alpha
        (lt_trans hlam₁ hlt) ha b₂,
      C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha hlam₁ ha b₁]
  exact KummerCoefficients.kummerSeries_strictAnti_lambda
    lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hlt (by positivity)

/-- Strict λ-antitonicity of the intrinsic source-Gram diagonal trace. -/
theorem C_intrinsicEntire_Gram_trace_strictAnti_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlt : lam₁ < lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₂ alpha (lt_trans hlam₁ hlt) ha (b₂ i))
      (b₂ i))) <
    (∑' i : ι₁, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₁ alpha hlam₁ ha (b₁ i)) (b₁ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₂ alpha
        (lt_trans hlam₁ hlt) ha b₂,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₁ alpha hlam₁ ha b₁]
  exact KummerCoefficients.kummerSeries_strictAnti_lambda
    lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hlt (by positivity)

/-- Equality of exact S₂ energies, even on unrelated complete
source Hilbert bases, identifies the positive ultraspherical parameter. -/
theorem C_intrinsicEntire_HS_energy_identifies_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (heq :
      (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) =
      (∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha hlam₂ ha (b₂ i)‖ ^ 2)) :
    lam₁ = lam₂ := by
  rcases lt_trichotomy lam₁ lam₂ with hlt | hequal | hgt
  · have hstrict := C_intrinsicEntire_HS_energy_strictAnti_lambda
      lam₁ lam₂ alpha hlam₁ hlt ha b₁ b₂
    exact False.elim (hstrict.ne heq.symm)
  · exact hequal
  · have hstrict := C_intrinsicEntire_HS_energy_strictAnti_lambda
      lam₂ lam₁ alpha hlam₂ hgt ha b₂ b₁
    exact False.elim (hstrict.ne heq)

/-- The scalar diagonal trace of the actual source Gram uniquely
identifies λ at fixed α, independently of each complete source basis. -/
theorem C_intrinsicEntire_Gram_trace_identifies_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂)))
    (heq :
      (∑' i : ι₁, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam₁ alpha hlam₁ ha (b₁ i)) (b₁ i))) =
      (∑' i : ι₂, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam₂ alpha hlam₂ ha (b₂ i)) (b₂ i)))) :
    lam₁ = lam₂ := by
  rcases lt_trichotomy lam₁ lam₂ with hlt | hequal | hgt
  · have hstrict := C_intrinsicEntire_Gram_trace_strictAnti_lambda
      lam₁ lam₂ alpha hlam₁ hlt ha b₁ b₂
    exact False.elim (hstrict.ne heq.symm)
  · exact hequal
  · have hstrict := C_intrinsicEntire_Gram_trace_strictAnti_lambda
      lam₂ lam₁ alpha hlam₂ hgt ha b₂ b₁
    exact False.elim (hstrict.ne heq)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_strictAnti_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_strictAnti_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_identifies_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_identifies_lambda

end GegenbauerFock.GeneralUltrasphericalFock
