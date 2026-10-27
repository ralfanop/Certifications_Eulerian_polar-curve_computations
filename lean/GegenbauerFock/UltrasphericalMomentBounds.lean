import GegenbauerFock.UltrasphericalMeasure

/-!
# V007: integrability and bounds of ALL ultraspherical even moments

These theorems concern the genuine Beta-pushforward probability measure,
not a postulated weight or a finite-dimensional approximation.
The exact general Pochhammer quotient for each even moment, odd moment
vanishing and the Gamma density change-of-variables are separate
formalization targets.
-/

open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- Actual degree-2n moment of the ultraspherical probability measure. -/
noncomputable def evenMoment (lam : ℝ) (n : ℕ) : ℝ :=
  ∫ u : ℝ, u ^ (2 * n) ∂(measure lam)

/-- Every degree-2n moment integrand is truly Bochner integrable. -/
theorem evenMoment_integrable (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) :
    Integrable (fun u : ℝ => u ^ (2 * n)) (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [ae_mem_unit_interval lam] with u hu
  have habs : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
  calc
    ‖u ^ (2 * n)‖ = |u| ^ (2 * n) := by simp [norm_pow]
    _ ≤ (1 : ℝ) ^ (2 * n) := by gcongr
    _ = 1 := by simp

/-- Each even ultraspherical moment is nonnegative. -/
theorem evenMoment_nonneg (lam : ℝ) (n : ℕ) :
    0 ≤ evenMoment lam n := by
  unfold evenMoment
  apply integral_nonneg
  intro u
  change (0 : ℝ) ≤ u ^ (2 * n)
  rw [show 2 * n = n * 2 by omega, pow_mul]
  positivity

/-- Every even ultraspherical probability moment is at most one. -/
theorem evenMoment_le_one (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) :
    evenMoment lam n ≤ 1 := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  calc
    evenMoment lam n ≤ ∫ _u : ℝ, (1 : ℝ) ∂(measure lam) := by
      apply integral_mono_ae (evenMoment_integrable lam hlam n) (integrable_const 1)
      filter_upwards [ae_mem_unit_interval lam] with u hu
      have habs : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
      have hu : u ^ (2 * n) ≤ |u| ^ (2 * n) := by
        rw [← abs_pow]
        exact le_abs_self _
      calc
        u ^ (2 * n) ≤ |u| ^ (2 * n) := hu
        _ ≤ (1 : ℝ) ^ (2 * n) := by gcongr
        _ = 1 := by simp
    _ = 1 := integral_one lam hlam

/-- Complete elementary probability bounds on general-λ even moments. -/
theorem evenMoment_bounds (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    0 ≤ evenMoment lam n ∧ evenMoment lam n ≤ 1 :=
  ⟨evenMoment_nonneg lam n, evenMoment_le_one lam hlam n⟩

/-- The zeroth even moment is exactly the normalized total mass. -/
theorem evenMoment_zero (lam : ℝ) (hlam : 0 < lam) :
    evenMoment lam 0 = 1 := by
  simpa [evenMoment] using integral_one lam hlam

/-- For every positive ultraspherical parameter, consecutive even moments
decrease. This uses the actual support of the Beta-pushforward law and
the genuine Bochner integral, not the still-open closed Pochhammer formula. -/
theorem evenMoment_succ_le (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    evenMoment lam (n + 1) ≤ evenMoment lam n := by
  unfold evenMoment
  apply integral_mono_ae
    (evenMoment_integrable lam hlam (n + 1))
    (evenMoment_integrable lam hlam n)
  filter_upwards [ae_mem_unit_interval lam] with u hu
  have h1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have h2 : 0 ≤ 1 + u := by linarith [hu.1]
  have hu2 : u ^ 2 ≤ (1 : ℝ) := by
    nlinarith [mul_nonneg h1 h2]
  have hnonneg : 0 ≤ u ^ (2 * n) := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
    positivity
  calc
    u ^ (2 * (n + 1)) = u ^ (2 * n) * u ^ 2 := by
      rw [mul_add, mul_one, pow_add]
    _ ≤ u ^ (2 * n) * 1 :=
      mul_le_mul_of_nonneg_left hu2 hnonneg
    _ = u ^ (2 * n) := by ring

#print axioms GegenbauerFock.Ultraspherical.evenMoment_integrable
#print axioms GegenbauerFock.Ultraspherical.evenMoment_succ_le
#print axioms GegenbauerFock.Ultraspherical.evenMoment_bounds
#print axioms GegenbauerFock.Ultraspherical.evenMoment_zero

end GegenbauerFock.Ultraspherical
