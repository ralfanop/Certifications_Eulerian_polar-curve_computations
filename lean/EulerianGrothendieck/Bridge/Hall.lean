import EulerianGrothendieck.GaussianFockBridge
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Propositions 3.4–3.5: Hall and Bargmann normalisations

Manuscript V173, eqs. (27)–(29) and (30)–(33).

Hall's one-dimensional transform is taken as the integral (29)
`(𝒱_ħ u)(w) = (πħ)^{-1/4} ∫ exp((√8 w x - w² - x²)/(2ħ)) u(x) dx`.
Its unitarity (Hall, Thm. 14.18) and Melzak's product for `π/(2e)` are cited inputs; neither is
needed for the identities proved here, except Melzak's product for (bargmann-melzak-product),
where it is an explicit hypothesis.
-/

open MeasureTheory Complex Set intervalIntegral Filter Topology

namespace EulerianBridge.Hall

open EulerianGrothendieck.Fock

/-- Hall's transform (29). -/
noncomputable def hall (ħ : ℝ) (u : ℝ → ℂ) (w : ℂ) : ℂ :=
  (((Real.pi * ħ) ^ (-(1:ℝ) / 4) : ℝ) : ℂ) *
    ∫ x : ℝ, cexp ((Real.sqrt 8 * w * x - w ^ 2 - (x:ℂ) ^ 2) / (2 * ħ)) * u x

/-- `u_ħ(x) = e^{x²/(2ħ)} 1_{[-1/2,1/2]}(x)` (eq. (27)). -/
noncomputable def uħ (ħ : ℝ) (x : ℝ) : ℂ :=
  (Icc (-1/2:ℝ) (1/2)).indicator (fun x => cexp ((x:ℂ) ^ 2 / (2 * ħ))) x

/-- The Gaussian cancellation: `(𝒱_ħ u_ħ)(iħz/√2) = (πħ)^{-1/4} e^{ħz²/4} r_E(z)`. -/
theorem hall_uħ {ħ : ℝ} (hħ : 0 < ħ) (z : ℂ) :
    hall ħ (uħ ħ) (ħ * z * (I / Real.sqrt 2)) =
      (((Real.pi * ħ) ^ (-(1:ℝ) / 4) : ℝ) : ℂ) * cexp (ħ * z ^ 2 / 4) * rE z := by
  unfold hall uħ
  rw [mul_assoc (((Real.pi * ħ) ^ (-(1:ℝ) / 4) : ℝ) : ℂ)]
  congr 1
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hs8 : (Real.sqrt 8 : ℂ) = 2 * Real.sqrt 2 := by
    rw [show (8:ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    push_cast; ring
  have hsq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hħ' : (ħ : ℂ) ≠ 0 := by exact_mod_cast hħ.ne'
  have e : ∀ x : ℝ, cexp ((Real.sqrt 8 * (ħ * z * (I / Real.sqrt 2)) * x - (ħ * z * (I / Real.sqrt 2)) ^ 2
      - (x:ℂ) ^ 2) / (2 * ħ)) * (Icc (-1/2:ℝ) (1/2)).indicator (fun x => cexp ((x:ℂ) ^ 2 / (2 * ħ))) x
      = (Icc (-1/2:ℝ) (1/2)).indicator (fun x => cexp (ħ * z ^ 2 / 4) * cexp (I * x * z)) x := by
    intro x
    by_cases hx : x ∈ Icc (-1/2:ℝ) (1/2)
    · rw [indicator_of_mem hx, indicator_of_mem hx, ← Complex.exp_add, ← Complex.exp_add]
      congr 1
      rw [hs8]
      field_simp
      rw [hsq]
      linear_combination (-4 * (ħ:ℂ) ^ 2 * z ^ 2) * I_sq
    · rw [indicator_of_notMem hx, indicator_of_notMem hx, mul_zero]
  trans ∫ x : ℝ, (Icc (-1/2:ℝ) (1/2)).indicator (fun x => cexp (ħ * z ^ 2 / 4) * cexp (I * x * z)) x
  · exact MeasureTheory.integral_congr_ae (Eventually.of_forall e)
  rw [MeasureTheory.integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul]
  rfl

/-- Proposition 3.4, eq. (28): `r_E(z) = (πħ)^{1/4} e^{-ħz²/4} (𝒱_ħ u_ħ)(ħ z z₀)`, `z₀ = i/√2`. -/
theorem segal_result {ħ : ℝ} (hħ : 0 < ħ) (z : ℂ) :
    rE z = (((Real.pi * ħ) ^ ((1:ℝ) / 4) : ℝ) : ℂ) * cexp (-(ħ * z ^ 2 / 4)) *
      hall ħ (uħ ħ) (ħ * z * (I / Real.sqrt 2)) := by
  rw [hall_uħ hħ]
  have hp : 0 < Real.pi * ħ := by positivity
  have h1 : (((Real.pi * ħ) ^ ((1:ℝ) / 4) : ℝ) : ℂ) * (((Real.pi * ħ) ^ (-(1:ℝ) / 4) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.rpow_add hp]; norm_num
  have h2 : cexp (-(ħ * z ^ 2 / 4)) * cexp (ħ * z ^ 2 / 4) = 1 := by
    rw [← Complex.exp_add]; simp
  calc rE z = ((((Real.pi * ħ) ^ ((1:ℝ) / 4) : ℝ) : ℂ) * (((Real.pi * ħ) ^ (-(1:ℝ) / 4) : ℝ) : ℂ)) *
        (cexp (-(ħ * z ^ 2 / 4)) * cexp (ħ * z ^ 2 / 4)) * rE z := by rw [h1, h2]; ring
    _ = _ := by ring

/-! ## Proposition 3.5 -/

/-- `C_B := (π/e)^{1/4}`. -/
noncomputable def CB : ℝ := (Real.pi / Real.exp 1) ^ ((1:ℝ) / 4)

theorem rE_one_ne_zero : rE 1 ≠ 0 := by
  rw [rE_eq_sin_div one_ne_zero]
  have : Complex.sin (1 / 2) ≠ 0 := by
    rw [show (1:ℂ) / 2 = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, ← ofReal_sin]
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi (by norm_num) (by linarith [Real.two_le_pi])).ne'
  exact div_ne_zero this (by norm_num)

/-- `(𝒱₁u₁)(iz/√2) = e^{z²/4} r_E(z)/π^{1/4}`. -/
theorem hall_one (z : ℂ) :
    hall 1 (uħ 1) (z * (I / Real.sqrt 2)) = cexp (z ^ 2 / 4) * rE z / ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) := by
  have h := hall_uħ (ħ := 1) one_pos z
  rw [ofReal_one, one_mul, one_mul] at h
  rw [h, mul_one]
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  have hq : ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hp _).ne'
  have hinv : ((Real.pi ^ (-(1:ℝ) / 4) : ℝ) : ℂ) = 1 / ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) := by
    rw [show -(1:ℝ) / 4 = -((1:ℝ) / 4) by ring, Real.rpow_neg hp.le]; push_cast; ring
  rw [hinv]; field_simp

/-- `C_B = r_E(1)/(𝒱₁u₁)(i/√2) = (π/e)^{1/4}` (eq. (31)). -/
theorem CB_eq : (CB : ℂ) = rE 1 / hall 1 (uħ 1) (1 * (I / Real.sqrt 2)) := by
  rw [hall_one]
  have hr := rE_one_ne_zero
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  have he : cexp ((1:ℂ) ^ 2 / 4) = ((Real.exp 1 ^ ((1:ℝ) / 4) : ℝ) : ℂ) := by
    rw [← Real.exp_mul, one_mul, ofReal_exp]; push_cast; ring_nf
  rw [he]
  unfold CB
  rw [Real.div_rpow hp.le (Real.exp_pos 1).le]
  have h1 : ((Real.exp 1 ^ ((1:ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos (Real.exp_pos 1) _).ne'
  have h2 : ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.rpow_pos_of_pos hp _).ne'
  push_cast
  field_simp

theorem CB_complex : (CB : ℂ) = ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) / cexp (1 / 4) := by
  unfold CB
  rw [Real.div_rpow Real.pi_pos.le (Real.exp_pos 1).le, Real.exp_one_rpow, ofReal_div, ofReal_exp]
  congr 2; norm_num

/-- Eq. (segal-isolated-profile): `r_E(z) = C_B e^{-(z²-1)/4} (𝒱₁u₁)(z z₀)`. -/
theorem isolated_profile (z : ℂ) :
    rE z = (CB : ℂ) * cexp (-((z ^ 2 - 1) / 4)) * hall 1 (uħ 1) (z * (I / Real.sqrt 2)) := by
  rw [hall_one, CB_complex]
  have h2 : ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hx : cexp (-((z ^ 2 - 1) / 4)) * cexp (z ^ 2 / 4) = cexp (1 / 4) := by
    rw [← Complex.exp_add]; congr 1; ring
  calc rE z = (((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ) / ((Real.pi ^ ((1:ℝ) / 4) : ℝ) : ℂ)) *
        ((cexp (-((z ^ 2 - 1) / 4)) * cexp (z ^ 2 / 4)) / cexp (1 / 4)) * rE z := by
        rw [div_self h2, hx, div_self (Complex.exp_ne_zero _)]; ring
    _ = _ := by ring

/-- Melzak's product (cited input, Melzak 1961, p. 39 (2)). -/
def MelzakProduct : Prop :=
  Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 (2 * N), (1 + 2 / (n:ℝ)) ^ ((-1:ℝ) ^ (n + 1) * n))
    atTop (𝓝 (Real.pi / (2 * Real.exp 1)))

/-- Eq. (bargmann-melzak-product): `C_B = (2 lim ∏ …)^{1/4}`, given Melzak's product. -/
theorem CB_melzak (h : MelzakProduct) :
    ∃ P : ℝ, Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 (2 * N), (1 + 2 / (n:ℝ)) ^ ((-1:ℝ) ^ (n + 1) * n))
      atTop (𝓝 P) ∧ CB = (2 * P) ^ ((1:ℝ) / 4) := by
  refine ⟨_, h, ?_⟩
  unfold CB; congr 1; field_simp

end EulerianBridge.Hall
