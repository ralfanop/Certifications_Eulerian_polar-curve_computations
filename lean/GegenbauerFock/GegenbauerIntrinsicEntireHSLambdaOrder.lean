import GegenbauerFock.GegenbauerIntrinsicEntireHSKummer
import GegenbauerFock.KummerPositiveBounds

/-!
# V007 — comparison of ultraspherical source parameters via exact Kummer mass

As λ increases, every nonvacuum Pochhammer quotient
(1/2)_n/(λ+1)_n decreases. The comparison is certified by the
actual recursive coefficients, then transferred through a summable
nonnegative real-series comparison to the unregularized Kummer
function and the true analytic entire Gaussian-Fock Hilbert–Schmidt
source-basis energy and Gram diagonal trace.

The two ultraspherical source Hilbert spaces differ; the comparison is
only between scalar basis-independent mass invariants, and explicitly
allows unrelated complete source Hilbert bases.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.KummerCoefficients

/-- Every rising-factorial Kummer ratio is antitone in the positive
ultraspherical parameter λ, for all natural n including n=0. -/
theorem ratio_antitone_lambda
    (lam₁ lam₂ : ℝ) (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂)
    (n : ℕ) : ratio lam₂ n ≤ ratio lam₁ n := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hle
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ratio_succ, ratio_succ]
      have hnum : 0 ≤ (n : ℝ) + 1 / 2 := by positivity
      have hd₁ : 0 < (n : ℝ) + lam₁ + 1 := by positivity
      have hd₂ : 0 < (n : ℝ) + lam₂ + 1 := by positivity
      calc
        ratio lam₂ n * ((n : ℝ) + 1 / 2) /
            ((n : ℝ) + lam₂ + 1) ≤
          ratio lam₁ n * ((n : ℝ) + 1 / 2) /
            ((n : ℝ) + lam₂ + 1) := by
              apply div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right ih hnum) hd₂.le
        _ ≤ ratio lam₁ n * ((n : ℝ) + 1 / 2) /
            ((n : ℝ) + lam₁ + 1) := by
              apply div_le_div_of_nonneg_left
                (mul_nonneg (ratio_nonneg lam₁ hlam₁ n) hnum)
                hd₁
              linarith

/-- At any nonnegative Kummer argument, a larger positive λ
cannot increase the exact unregularized real Kummer mass. -/
theorem kummerSeries_antitone_lambda
    (lam₁ lam₂ z : ℝ) (hlam₁ : 0 < lam₁)
    (hle : lam₁ ≤ lam₂) (hz : 0 ≤ z) :
    kummerSeries lam₂ z ≤ kummerSeries lam₁ z := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hle
  have hleft := kummerSeries_summable lam₂ z hlam₂ hz
  have hright := kummerSeries_summable lam₁ z hlam₁ hz
  unfold kummerSeries
  exact hleft.tsum_le_tsum
    (fun n => mul_le_mul_of_nonneg_right
      (ratio_antitone_lambda lam₁ lam₂ hlam₁ hle n)
      (by positivity))
    hright

#print axioms GegenbauerFock.KummerCoefficients.ratio_antitone_lambda
#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_antitone_lambda

end GegenbauerFock.KummerCoefficients

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Comparing λ across DIFFERENT source L² Gaussian entire-Fock
transforms: the whole S₂ mass is antitone in λ for fixed α>0,
independently of the two unrelated complete source Hilbert bases. -/
theorem C_intrinsicEntire_HS_energy_antitone_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂,
      ‖C_intrinsicEntire lam₂ alpha (lt_of_lt_of_le hlam₁ hle) ha (b₂ i)‖ ^ 2) ≤
      (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₂ alpha
        (lt_of_lt_of_le hlam₁ hle) ha b₂,
      C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha hlam₁ ha b₁]
  exact KummerCoefficients.kummerSeries_antitone_lambda
    lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hle (by positivity)

/-- Identical positive-parameter comparison for the genuine
analytic-Fock intrinsic source-Gram diagonal Hilbert traces. -/
theorem C_intrinsicEntire_Gram_trace_antitone_lambda
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (∑' i : ι₂, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₂ alpha (lt_of_lt_of_le hlam₁ hle) ha (b₂ i))
      (b₂ i))) ≤
    (∑' i : ι₁, RCLike.re (inner ℂ
      (C_intrinsicEntire_gram lam₁ alpha hlam₁ ha (b₁ i)) (b₁ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₂ alpha
        (lt_of_lt_of_le hlam₁ hle) ha b₂,
      C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₁ alpha hlam₁ ha b₁]
  exact KummerCoefficients.kummerSeries_antitone_lambda
    lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hle (by positivity)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_antitone_lambda
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_antitone_lambda

end GegenbauerFock.GeneralUltrasphericalFock
