/-
# Section 3.7 of the V001 manuscript: energy of the radial profile

* Eq. (45): `E_tot = (1/π) ∫_{-π}^{π} r_E² = (4/π) Si(π) − 8/π²` (integration by parts with the
  antiderivative `2 Si(θ) − θ sinc(θ/2)²` of `r_E²`).
* Eq. (46): Plancherel, `E_tot = A₀²/2 + ∑_{n ≥ 1} A_n²` (from Mathlib's Parseval identity on
  `AddCircle (2π)` applied to the lift `FourierSeries.F` of `r_E`).
* Eq. (47): the mean-square residual of the projection,
  `(1/2π) ∫ (r_E − r_L)² = ½ (E_tot − A₀²/2 − A₁²)`.
The decimals of Eq. (47), Eq. (48) and Table 1 are certified by interval arithmetic (README §2).
-/
import EulerianCert.Projection
import EulerianCert.FourierSeries

open Real intervalIntegral MeasureTheory
open EulerianCert.FourierModes EulerianCert.FourierSeries

noncomputable section

namespace EulerianCert.Energy

/-- The total radial energy `E_tot = (1/π) ∫_{-π}^{π} r_E²` (Eq. (45)). -/
def Etot : ℝ := (1 / π) * ∫ θ in (-π)..π, rE θ ^ 2

/-! ### Plancherel, Eq. (46) -/

lemma integral_haar_normSq :
    (∫ t, ‖F t‖ ^ 2 ∂AddCircle.haarAddCircle) = (1 / (2 * π)) * ∫ θ in (-π)..π, rE θ ^ 2 := by
  rw [AddCircle.integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage (2 * π) (-π)]
  have hb : -π + 2 * π = π := by ring
  rw [hb, smul_eq_mul, one_div]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [Set.uIcc_of_le (by linarith [pi_pos])] at hθ
  simp only
  rw [F_coe, ρ_eq hθ, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Eq. (46)**: `(1/π) ∫ r_E² = A₀²/2 + ∑_{n ≥ 1} A_n²`. -/
theorem plancherel : HasSum (fun n : ℕ => A (n + 1) ^ 2) (Etot - A 0 ^ 2 / 2) := by
  have h := hasSum_sq_fourierCoeff (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F)
  simp_rw [fourierCoeff_toLp] at h
  have hint : (∫ t, ‖(ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F) t‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∫ t, ‖F t‖ ^ 2 ∂AddCircle.haarAddCircle := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toAEEqFun AddCircle.haarAddCircle F] with t ht
    rw [← ht]; rfl
  rw [hint, integral_haar_normSq] at h
  simp_rw [fourierCoeff_F, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  have h2 := h.nat_add_neg
  simp only [Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_zero] at h2
  -- h2 : HasSum (fun n => (A n / 2)^2 + (A n / 2)^2) ((1/(2π)) ∫ r_E² + (A 0 / 2)^2)
  have h3 : HasSum (fun n : ℕ => A n ^ 2) (Etot + A 0 ^ 2 / 2) := by
    have := h2.mul_left 2
    convert this using 1
    · ext n; ring
    · rw [Etot]; have : π ≠ 0 := pi_ne_zero; field_simp
  rw [← hasSum_nat_add_iff' 1] at h3
  simp only [Finset.range_one, Finset.sum_singleton] at h3
  convert h3 using 1
  ring

/-! ### The closed form, Eq. (45) -/

lemma hasDerivAt_Si (x : ℝ) : HasDerivAt Si (sinc x) x :=
  (continuous_sinc.integral_hasStrictDerivAt 0 x).hasDerivAt

/-- Antiderivative of `r_E²`. -/
def G (θ : ℝ) : ℝ := 2 * Si θ - θ * sinc (θ / 2) ^ 2

lemma continuous_G : Continuous G := by
  have hSi : Continuous Si := continuous_iff_continuousAt.2 fun x => (hasDerivAt_Si x).continuousAt
  unfold G
  have := continuous_sinc
  fun_prop

lemma hasDerivAt_G {θ : ℝ} (hθ : θ ≠ 0) : HasDerivAt G (rE θ ^ 2) θ := by
  -- near θ, θ sinc(θ/2)² = 4 sin(θ/2)²/θ
  have heq : (fun t => t * sinc (t / 2) ^ 2) =ᶠ[nhds θ] (fun t => 4 * Real.sin (t / 2) ^ 2 / t) := by
    filter_upwards [isOpen_ne.mem_nhds hθ] with t ht
    rw [sinc_of_ne_zero (div_ne_zero ht two_ne_zero)]
    field_simp
    ring
  have h1 : HasDerivAt (fun t => 4 * Real.sin (t / 2) ^ 2 / t)
      ((4 * (2 * Real.sin (θ / 2) * (Real.cos (θ / 2) * (1 / 2))) * θ - 4 * Real.sin (θ / 2) ^ 2 * 1)
        / θ ^ 2) θ := by
    have hs : HasDerivAt (fun t => Real.sin (t / 2)) (Real.cos (θ / 2) * (1 / 2)) θ := by
      have := ((hasDerivAt_id' θ).div_const 2).sin
      simpa using this
    have := ((hs.pow 2).const_mul 4).div (hasDerivAt_id' θ) hθ
    convert this using 1
    simp
  have h2 := h1.congr_of_eventuallyEq heq
  have h3 := ((hasDerivAt_Si θ).const_mul 2).sub h2
  unfold G
  convert h3 using 1
  rw [rE_of_ne_zero hθ, sinc_of_ne_zero hθ]
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [hsin]
  field_simp
  ring

lemma integral_rE_sq_half : (∫ θ in (0 : ℝ)..π, rE θ ^ 2) = 2 * Si π - 4 / π := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le pi_pos.le continuous_G.continuousOn
    (fun θ hθ => hasDerivAt_G hθ.1.ne') ((continuous_rE.pow 2).intervalIntegrable _ _)]
  simp only [G, Si, intervalIntegral.integral_same, mul_zero, zero_div, sinc_zero, zero_mul,
    sub_zero]
  rw [sinc_of_ne_zero (div_ne_zero pi_ne_zero two_ne_zero), Real.sin_pi_div_two]
  have : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-- **Eq. (45)**: `E_tot = (4/π) Si(π) − 8/π²`. -/
theorem Etot_closed : Etot = 4 / π * Si π - 8 / π ^ 2 := by
  have hsym : (∫ θ in (-π)..π, rE θ ^ 2) = 2 * ∫ θ in (0 : ℝ)..π, rE θ ^ 2 := by
    have hc : Continuous (fun θ => rE θ ^ 2) := continuous_rE.pow 2
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π) (fun θ => rE θ ^ 2)
    simp only [neg_zero, rE_neg] at h
    rw [← h]; ring
  rw [Etot, hsym, integral_rE_sq_half]
  have : π ≠ 0 := pi_ne_zero
  field_simp
  ring

/-! ### The mean-square residual, Eq. (47) -/

/-- **Eq. (47)**: `(1/2π) ∫ (r_E − r_L)² = ½ (E_tot − A₀²/2 − A₁²)`. -/
theorem rms_residual :
    (1 / (2 * π)) * (∫ θ in (-π)..π, (rE θ - bE - aE * Real.cos θ) ^ 2) =
      (1 / 2) * (Etot - A 0 ^ 2 / 2 - A 1 ^ 2) := by
  rw [Projection.expand, Etot, bE, aE]
  have : π ≠ 0 := pi_ne_zero
  field_simp
  ring

end EulerianCert.Energy
