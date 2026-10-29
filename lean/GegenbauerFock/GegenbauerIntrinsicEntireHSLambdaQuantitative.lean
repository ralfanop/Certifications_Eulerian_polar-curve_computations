import GegenbauerFock.GegenbauerIntrinsicEntireHSLambdaOrder

/-!
# V007 — quantitative lower separation in the ultraspherical lambda parameter

The difference between exact unregularized Kummer masses for λ₁ ≤ λ₂
is bounded below by the difference of their first excited coefficients.
This yields the explicit nonzero quantitative separation at fixed α>0:

H(λ₁,α)-H(λ₂,α) ≥ (λ₂-λ₁)/(8α(λ₁+1)(λ₂+1)).

The statement is transferred to the real analytic Gaussian-Fock
source-basis Hilbert–Schmidt energy and intrinsic source-Gram trace.
The two source bases may belong to different Hilbert spaces.
-/

noncomputable section

namespace GegenbauerFock.KummerCoefficients

/-- The gap between nonnegative-argument Kummer masses dominates
the complete difference of the first nonvacuum terms. -/
theorem kummerSeries_lambda_first_gap
    (lam₁ lam₂ z : ℝ)
    (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) (hz : 0 ≤ z) :
    (ratio lam₁ 1 - ratio lam₂ 1) * z ≤
      kummerSeries lam₁ z - kummerSeries lam₂ z := by
  have hlam₂ : 0 < lam₂ := lt_of_lt_of_le hlam₁ hle
  let f₁ : ℕ → ℝ := fun n =>
    ratio lam₁ n * (z ^ n / (Nat.factorial n : ℝ))
  let f₂ : ℕ → ℝ := fun n =>
    ratio lam₂ n * (z ^ n / (Nat.factorial n : ℝ))
  have hs₁ : Summable f₁ := kummerSeries_summable lam₁ z hlam₁ hz
  have hs₂ : Summable f₂ := kummerSeries_summable lam₂ z hlam₂ hz
  have hterm (n : ℕ) : f₂ n ≤ f₁ n := by
    exact mul_le_mul_of_nonneg_right
      (ratio_antitone_lambda lam₁ lam₂ hlam₁ hle n) (by positivity)
  have hs_diff : Summable (fun n => f₁ n - f₂ n) := hs₁.sub hs₂
  have hfirst_le :
      f₁ 1 - f₂ 1 ≤ ∑' n, (f₁ n - f₂ n) :=
    hs_diff.le_tsum 1 (fun n _ => sub_nonneg.mpr (hterm n))
  have hfirst :
      f₁ 1 - f₂ 1 = (ratio lam₁ 1 - ratio lam₂ 1) * z := by
    dsimp [f₁, f₂]
    norm_num
    ring
  have hsum :
      (∑' n, (f₁ n - f₂ n)) =
        kummerSeries lam₁ z - kummerSeries lam₂ z := by
    calc
      (∑' n, (f₁ n - f₂ n)) =
          (∑' n, f₁ n) - (∑' n, f₂ n) := hs₁.tsum_sub hs₂
      _ = kummerSeries lam₁ z - kummerSeries lam₂ z := rfl
  calc
    (ratio lam₁ 1 - ratio lam₂ 1) * z = f₁ 1 - f₂ 1 := hfirst.symm
    _ ≤ ∑' n, (f₁ n - f₂ n) := hfirst_le
    _ = kummerSeries lam₁ z - kummerSeries lam₂ z := hsum

/-- Exact rational form of the first-term gap for z=1/(4α). -/
theorem ratio_lambda_first_gap_gaussian_exact
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hlam₂ : 0 < lam₂) (ha : 0 < alpha) :
    (ratio lam₁ 1 - ratio lam₂ 1) * (1 / (4 * alpha)) =
      (lam₂ - lam₁) /
        (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) := by
  have hd₁ : lam₁ + 1 ≠ 0 := ne_of_gt (by linarith)
  have hd₂ : lam₂ + 1 ≠ 0 := ne_of_gt (by linarith)
  have ha' : alpha ≠ 0 := ne_of_gt ha
  simp only [ratio_succ, ratio_zero, Nat.cast_zero, zero_add, one_mul]
  field_simp [hd₁, hd₂, ha']
  ring

#print axioms GegenbauerFock.KummerCoefficients.kummerSeries_lambda_first_gap
#print axioms GegenbauerFock.KummerCoefficients.ratio_lambda_first_gap_gaussian_exact

end GegenbauerFock.KummerCoefficients

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Quantitative strict-separation lower bound for genuine analytic
Gaussian-Fock S₂ energies at the same α but different source λ. -/
theorem C_intrinsicEntire_HS_energy_lambda_quantitative_gap
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (lam₂ - lam₁) / (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) ≤
      (∑' i : ι₁,
        ‖C_intrinsicEntire lam₁ alpha hlam₁ ha (b₁ i)‖ ^ 2) -
      (∑' i : ι₂,
        ‖C_intrinsicEntire lam₂ alpha (lt_of_lt_of_le hlam₁ hle) ha (b₂ i)‖ ^ 2) := by
  rw [C_intrinsicEntire_HS_energy_eq_kummer lam₁ alpha hlam₁ ha b₁,
    C_intrinsicEntire_HS_energy_eq_kummer lam₂ alpha
      (lt_of_lt_of_le hlam₁ hle) ha b₂]
  calc
    (lam₂ - lam₁) / (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) =
        (KummerCoefficients.ratio lam₁ 1 - KummerCoefficients.ratio lam₂ 1) *
          (1 / (4 * alpha)) :=
      (KummerCoefficients.ratio_lambda_first_gap_gaussian_exact
        lam₁ lam₂ alpha hlam₁ (lt_of_lt_of_le hlam₁ hle) ha).symm
    _ ≤ KummerCoefficients.kummerSeries lam₁ (1 / (4 * alpha)) -
          KummerCoefficients.kummerSeries lam₂ (1 / (4 * alpha)) :=
      KummerCoefficients.kummerSeries_lambda_first_gap
        lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hle (by positivity)

/-- The same quantitative gap holds for the actual intrinsic source-Gram
real diagonal traces on unrelated complete ultraspherical source bases. -/
theorem C_intrinsicEntire_Gram_trace_lambda_quantitative_gap
    (lam₁ lam₂ alpha : ℝ)
    (hlam₁ : 0 < lam₁) (hle : lam₁ ≤ lam₂) (ha : 0 < alpha)
    {ι₁ ι₂ : Type*}
    (b₁ : HilbertBasis ι₁ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₁)))
    (b₂ : HilbertBasis ι₂ ℂ (Lp ℂ 2 (Ultraspherical.measure lam₂))) :
    (lam₂ - lam₁) / (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) ≤
      (∑' i : ι₁, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam₁ alpha hlam₁ ha (b₁ i)) (b₁ i))) -
      (∑' i : ι₂, RCLike.re (inner ℂ
        (C_intrinsicEntire_gram lam₂ alpha (lt_of_lt_of_le hlam₁ hle) ha (b₂ i))
        (b₂ i))) := by
  rw [C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₁ alpha hlam₁ ha b₁,
    C_intrinsicEntire_Gram_basis_trace_eq_kummer lam₂ alpha
      (lt_of_lt_of_le hlam₁ hle) ha b₂]
  calc
    (lam₂ - lam₁) / (8 * alpha * (lam₁ + 1) * (lam₂ + 1)) =
        (KummerCoefficients.ratio lam₁ 1 - KummerCoefficients.ratio lam₂ 1) *
          (1 / (4 * alpha)) :=
      (KummerCoefficients.ratio_lambda_first_gap_gaussian_exact
        lam₁ lam₂ alpha hlam₁ (lt_of_lt_of_le hlam₁ hle) ha).symm
    _ ≤ KummerCoefficients.kummerSeries lam₁ (1 / (4 * alpha)) -
          KummerCoefficients.kummerSeries lam₂ (1 / (4 * alpha)) :=
      KummerCoefficients.kummerSeries_lambda_first_gap
        lam₁ lam₂ (1 / (4 * alpha)) hlam₁ hle (by positivity)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_HS_energy_lambda_quantitative_gap
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_Gram_trace_lambda_quantitative_gap

end GegenbauerFock.GeneralUltrasphericalFock
