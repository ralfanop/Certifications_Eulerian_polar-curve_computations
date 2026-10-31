/-
# Corollary 3.5 of the V001 manuscript: the orthogonal first-harmonic projection

`r_L = b_E + a_E cos θ` is the orthogonal projection of `r_E` onto `span{1, cos θ}` in
`L²([-π, π])`: for all real `a, b`,
  `∫ (r_E − b − a cos)² = ∫ (r_E − b_E − a_E cos)² + 2π (b − b_E)² + π (a − a_E)²`,
so `r_L` is the unique minimiser (Eq. (26)), with `b_E = (2/π) Si(π/2)` (Eq. (27)) and
`a_E = (2/π)[Si(3π/2) − Si(π/2)]` (Eq. (28)).  The sharp uniform error, Eq. (29), is
`FourierSeries.projection_error`.
-/
import EulerianCert.FourierSeries

open Real intervalIntegral
open EulerianCert.FourierModes EulerianCert.FourierSeries

noncomputable section

namespace EulerianCert.Projection

lemma int_rE : (∫ θ in (-π)..π, rE θ) = 2 * π * bE := by
  have h : A 0 = (1 / π) * ∫ θ in (-π)..π, rE θ := by
    rw [A]; congr 1; congr 1; ext θ; simp
  rw [bE]
  have hπ : π ≠ 0 := pi_ne_zero
  rw [h]; field_simp

lemma int_rE_cos : (∫ θ in (-π)..π, rE θ * Real.cos θ) = π * aE := by
  have h : A 1 = (1 / π) * ∫ θ in (-π)..π, rE θ * Real.cos θ := by
    rw [A]; congr 1; congr 1; ext θ; simp
  rw [aE]
  have hπ : π ≠ 0 := pi_ne_zero
  rw [h]; field_simp

lemma int_cos : (∫ θ in (-π)..π, Real.cos θ) = 0 := by
  rw [integral_cos]; simp

lemma int_cos_sq : (∫ θ in (-π)..π, Real.cos θ ^ 2) = π := by
  rw [integral_cos_sq]; simp

/-- Expansion of the quadratic error `H(b, a) = ∫ (r_E − b − a cos)²`. -/
lemma expand (b a : ℝ) :
    (∫ θ in (-π)..π, (rE θ - b - a * Real.cos θ) ^ 2) =
      (∫ θ in (-π)..π, rE θ ^ 2) - 2 * b * (2 * π * bE) - 2 * a * (π * aE) +
        2 * π * b ^ 2 + π * a ^ 2 := by
  have hr := continuous_rE
  have e : ∀ θ, (rE θ - b - a * Real.cos θ) ^ 2 =
      (rE θ ^ 2 - (2 * b) * rE θ) - (2 * a) * (rE θ * Real.cos θ) +
        (b ^ 2 + (2 * a * b) * Real.cos θ) + a ^ 2 * Real.cos θ ^ 2 := by
    intro θ; ring
  simp_rw [e]
  have i1 : IntervalIntegrable (fun θ => rE θ ^ 2) MeasureTheory.volume (-π) π :=
    (hr.pow 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => (2 * b) * rE θ) MeasureTheory.volume (-π) π :=
    (continuous_const.mul hr).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ => (2 * a) * (rE θ * Real.cos θ)) MeasureTheory.volume
      (-π) π := (continuous_const.mul (hr.mul Real.continuous_cos)).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun θ => b ^ 2 + (2 * a * b) * Real.cos θ) MeasureTheory.volume
      (-π) π := (continuous_const.add (continuous_const.mul Real.continuous_cos)).intervalIntegrable _ _
  have i5 : IntervalIntegrable (fun θ => a ^ 2 * Real.cos θ ^ 2) MeasureTheory.volume (-π) π :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have i6 : IntervalIntegrable (fun θ => (2 * a * b) * Real.cos θ) MeasureTheory.volume (-π) π :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((i1.sub i2).sub i3 |>.add i4) i5,
    intervalIntegral.integral_add ((i1.sub i2).sub i3) i4,
    intervalIntegral.integral_sub (i1.sub i2) i3, intervalIntegral.integral_sub i1 i2,
    intervalIntegral.integral_add intervalIntegrable_const i6,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    int_rE, int_rE_cos, int_cos, int_cos_sq, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_neg_eq_add]
  ring

/-- **Corollary 3.5, Eq. (26)**: Pythagorean identity for the projection. -/
theorem pythagoras (b a : ℝ) :
    (∫ θ in (-π)..π, (rE θ - b - a * Real.cos θ) ^ 2) =
      (∫ θ in (-π)..π, (rE θ - bE - aE * Real.cos θ) ^ 2) +
        2 * π * (b - bE) ^ 2 + π * (a - aE) ^ 2 := by
  rw [expand, expand]; ring

/-- `r_L = b_E + a_E cos` is the unique `L²` minimiser in `span{1, cos θ}`. -/
theorem projection_unique_min (b a : ℝ) (hne : (b, a) ≠ (bE, aE)) :
    (∫ θ in (-π)..π, (rE θ - bE - aE * Real.cos θ) ^ 2) <
      ∫ θ in (-π)..π, (rE θ - b - a * Real.cos θ) ^ 2 := by
  rw [pythagoras b a]
  have hπ := pi_pos
  by_cases hb : b = bE
  · have ha : a ≠ aE := fun ha => hne (by rw [hb, ha])
    have : 0 < (a - aE) ^ 2 := by positivity
    nlinarith [sq_nonneg (b - bE)]
  · have : 0 < (b - bE) ^ 2 := by positivity
    nlinarith [sq_nonneg (a - aE)]

/-- **Corollary 3.5, Eqs. (27)–(28)**: the projection coefficients via `Si`. -/
theorem coefficients :
    bE = (2 / π) * Si (π / 2) ∧ aE = (2 / π) * (Si (3 * π / 2) - Si (π / 2)) := by
  constructor
  · rw [bE, A_zero]; ring
  · rw [aE, A_succ_eq_Si 1 le_rfl]
    congr 2 <;> congr 1 <;> push_cast <;> ring

end EulerianCert.Projection
