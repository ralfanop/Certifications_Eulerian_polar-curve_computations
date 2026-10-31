/-
# Proposition 3.1 of the V001 manuscript (Eulerian cosine coefficients) and Definition 2.1

Numbering: V001 (22 October 2026); V478 has the same statement numbers in Section 3.

* `rE θ = sinc (θ/2)`: the Eulerian radius of Eq. (2), with the removable value `rE 0 = 1`
  (the function `EulerianCert.rE` of `Corner` is `2 sin(θ/2)/θ`, equal to it for `θ ≠ 0`).
* `Si x = ∫₀ˣ sinc`: the sine integral of Definition 2.1, Eq. (4), on the real line.
* `A n = (1/π) ∫_{-π}^{π} rE θ cos(nθ) dθ`: the cosine coefficients of Eq. (5).

Proved here (Proposition 3.1):
* Eqs. (6)–(7): `A 0 = (4/π) Si(π/2)` and `A n = (2/π)[Si((n+½)π) − Si((n−½)π)]`;
* Eq. (8): `A n = (−1)^{n+1} (4/π) ∫₀^{π/2} s sin s /(n²π² − s²) ds` for `n ≥ 1`;
* sign `(−1)^{n+1}`, strict decrease of `|A n|`, and the two-sided bound Eq. (9);
* absolute summability of the coefficients.
The Fourier identification (absolute and uniform convergence to `rE`) and Eq. (10) are in
`EulerianCert.FourierSeries`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.PSeries

open Real intervalIntegral Set

noncomputable section

namespace EulerianCert.FourierModes

/-! ### The radius, the sine integral and the coefficients -/

/-- The Eulerian radius `rE θ = 2 sin(θ/2)/θ`, `rE 0 = 1` (Eq. (2)). -/
def rE (θ : ℝ) : ℝ := sinc (θ / 2)

/-- The real sine integral `Si x = ∫₀ˣ sin t / t dt` (Definition 2.1). -/
def Si (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, sinc t

/-- The cosine coefficients of `rE` on `[-π, π]` (Eq. (5)). -/
def A (n : ℕ) : ℝ := (1 / π) * ∫ θ in (-π)..π, rE θ * Real.cos (n * θ)

/-- The positive integral of Eq. (8). -/
def I (n : ℕ) : ℝ := ∫ s in (0 : ℝ)..(π / 2), s * Real.sin s / ((n : ℝ) ^ 2 * π ^ 2 - s ^ 2)

lemma rE_of_ne_zero {θ : ℝ} (hθ : θ ≠ 0) : rE θ = 2 * Real.sin (θ / 2) / θ := by
  have h2 : θ / 2 ≠ 0 := div_ne_zero hθ two_ne_zero
  rw [rE, sinc_of_ne_zero h2]
  field_simp

@[simp] lemma rE_zero : rE 0 = 1 := by simp [rE]

lemma rE_neg (θ : ℝ) : rE (-θ) = rE θ := by
  simp [rE, neg_div]

lemma continuous_rE : Continuous rE :=
  continuous_sinc.comp (continuous_id.div_const 2)

lemma rE_pi : rE π = 2 / π := by
  rw [rE_of_ne_zero pi_ne_zero, Real.sin_pi_div_two, mul_one]

lemma Si_neg (x : ℝ) : Si (-x) = -Si x := by
  unfold Si
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) sinc
  simp only [sinc_neg, neg_zero] at h
  -- h : ∫ t in 0..x, sinc t = ∫ t in -x..0, sinc t
  rw [h, intervalIntegral.integral_symm]

/-! ### Elementary identities -/

/-- `rE θ cos(nθ) = a sinc(aθ) − b sinc(bθ)` with `a = n + ½`, `b = n − ½`, for every `θ`. -/
lemma rE_mul_cos (n : ℕ) (θ : ℝ) :
    rE θ * Real.cos (n * θ) =
      ((n : ℝ) + 1 / 2) * sinc (((n : ℝ) + 1 / 2) * θ) -
        ((n : ℝ) - 1 / 2) * sinc (((n : ℝ) - 1 / 2) * θ) := by
  rcases eq_or_ne θ 0 with rfl | hθ
  · simp; norm_num
  have ha : ((n : ℝ) + 1 / 2) ≠ 0 := by positivity
  rcases eq_or_ne ((n : ℝ) - 1 / 2) 0 with hb | hb
  · exfalso
    have : (2 * n : ℝ) = 1 := by linarith
    have h' : (2 * n : ℕ) = 1 := by exact_mod_cast this
    omega
  rw [rE_of_ne_zero hθ, sinc_of_ne_zero (mul_ne_zero ha hθ), sinc_of_ne_zero (mul_ne_zero hb hθ)]
  have hsa : Real.sin (((n : ℝ) + 1 / 2) * θ) =
      Real.sin (n * θ) * Real.cos (θ / 2) + Real.cos (n * θ) * Real.sin (θ / 2) := by
    rw [← Real.sin_add]; ring_nf
  have hsb : Real.sin (((n : ℝ) - 1 / 2) * θ) =
      Real.sin (n * θ) * Real.cos (θ / 2) - Real.cos (n * θ) * Real.sin (θ / 2) := by
    rw [← Real.sin_sub]; ring_nf
  have key : ∀ c : ℝ, c ≠ 0 → c * (Real.sin (c * θ) / (c * θ)) = Real.sin (c * θ) / θ := by
    intro c hc; field_simp
  rw [key _ ha, key _ hb, hsa, hsb]
  field_simp
  ring

lemma intervalIntegrable_sinc (a b : ℝ) : IntervalIntegrable sinc MeasureTheory.volume a b :=
  continuous_sinc.intervalIntegrable a b

/-- `∫₀^π c sinc(cθ) dθ = Si(cπ)` for `c ≠ 0`. -/
lemma integral_scaled_sinc {c : ℝ} (hc : c ≠ 0) :
    (∫ θ in (0 : ℝ)..π, c * sinc (c * θ)) = Si (c * π) := by
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ hc,
    mul_zero, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rfl

lemma integral_rE_mul_cos_half (n : ℕ) :
    (∫ θ in (0 : ℝ)..π, rE θ * Real.cos (n * θ)) =
      Si (((n : ℝ) + 1 / 2) * π) - Si (((n : ℝ) - 1 / 2) * π) := by
  have ha : ((n : ℝ) + 1 / 2) ≠ 0 := by positivity
  have hb : ((n : ℝ) - 1 / 2) ≠ 0 := by
    intro h
    have : (2 * n : ℝ) = 1 := by linarith
    have h' : (2 * n : ℕ) = 1 := by exact_mod_cast this
    omega
  simp_rw [rE_mul_cos n]
  rw [intervalIntegral.integral_sub, integral_scaled_sinc ha, integral_scaled_sinc hb]
  · exact (continuous_const.mul (continuous_sinc.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _
  · exact (continuous_const.mul (continuous_sinc.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _

lemma continuous_rE_mul_cos (n : ℕ) : Continuous (fun θ => rE θ * Real.cos (n * θ)) :=
  continuous_rE.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))

/-- Evenness: `∫_{-π}^{π} = 2 ∫_0^π` for the integrand of `A n`. -/
lemma integral_symm_halves (n : ℕ) :
    (∫ θ in (-π)..π, rE θ * Real.cos (n * θ)) = 2 * ∫ θ in (0 : ℝ)..π, rE θ * Real.cos (n * θ) := by
  have hc := continuous_rE_mul_cos n
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π)
    (fun θ => rE θ * Real.cos (n * θ))
  simp only [neg_zero, rE_neg, mul_neg, Real.cos_neg] at h
  rw [← h]
  ring

/-- Eqs. (6)–(7) in one formula: `A n = (2/π)[Si((n+½)π) − Si((n−½)π)]` for every `n`. -/
theorem A_eq_Si (n : ℕ) :
    A n = (2 / π) * (Si (((n : ℝ) + 1 / 2) * π) - Si (((n : ℝ) - 1 / 2) * π)) := by
  rw [A, integral_symm_halves, integral_rE_mul_cos_half]
  ring

/-- Eq. (6): `A 0 = (4/π) Si(π/2)`. -/
theorem A_zero : A 0 = (4 / π) * Si (π / 2) := by
  rw [A_eq_Si]
  have h1 : ((0 : ℕ) : ℝ) + 1 / 2 = 1 / 2 := by norm_num
  have h2 : ((0 : ℕ) : ℝ) - 1 / 2 = -(1 / 2) := by norm_num
  rw [h1, h2, neg_mul, Si_neg]
  ring_nf

/-- Eq. (7), in the manuscript's form `Si(π(2n±1)/2)`. -/
theorem A_succ_eq_Si (n : ℕ) (hn : 1 ≤ n) :
    A n = (2 / π) * (Si (π / 2 * (2 * n + 1)) - Si (π / 2 * (2 * n - 1))) := by
  rw [A_eq_Si]
  congr 2 <;> congr 1 <;> ring

/-! ### The sign representation, Eq. (8) -/

lemma sinc_shift (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : s ∈ uIcc (-(π / 2)) (π / 2)) :
    sinc (n * π + s) = (-1 : ℝ) ^ n * (Real.sin s / (n * π + s)) := by
  rw [uIcc_of_le (by linarith [pi_pos])] at hs
  have hpos : 0 < (n : ℝ) * π + s := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [pi_pos, hs.1]
  rw [sinc_of_ne_zero hpos.ne', add_comm ((n : ℝ) * π) s, Real.sin_add_nat_mul_pi]
  ring

lemma pair_identity (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) (π / 2)) :
    Real.sin s / (n * π + s) + Real.sin (-s) / (n * π + -s) =
      -2 * (s * Real.sin s / ((n : ℝ) ^ 2 * π ^ 2 - s ^ 2)) := by
  rw [uIcc_of_le (by linarith [pi_pos])] at hs
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < (n : ℝ) * π + s := by nlinarith [pi_pos, hs.1]
  have h2 : 0 < (n : ℝ) * π - s := by nlinarith [pi_pos, hs.2]
  have h3 : 0 < (n : ℝ) ^ 2 * π ^ 2 - s ^ 2 := by nlinarith
  rw [Real.sin_neg, ← sub_eq_add_neg ((n : ℝ) * π) s]
  field_simp
  ring

lemma s_sq_le {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) : s ^ 2 ≤ π ^ 2 / 4 := by
  have := mul_le_mul hs.2 hs.2 hs.1 (by linarith [pi_pos])
  nlinarith

lemma pi_sq_le {n : ℕ} (hn : 1 ≤ n) : π ^ 2 ≤ (n : ℝ) ^ 2 * π ^ 2 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg π) (sub_nonneg.2 this)]

lemma den_pos {n : ℕ} (hn : 1 ≤ n) {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) :
    3 * π ^ 2 / 4 ≤ (n : ℝ) ^ 2 * π ^ 2 - s ^ 2 := by
  have := s_sq_le hs; have := pi_sq_le hn; linarith

lemma continuousOn_kernel (n : ℕ) (hn : 1 ≤ n) :
    ContinuousOn (fun s : ℝ => s * Real.sin s / ((n : ℝ) ^ 2 * π ^ 2 - s ^ 2))
      (Icc 0 (π / 2)) := by
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro s hs
  have := den_pos hn hs
  have : 0 < 3 * π ^ 2 / 4 := by positivity
  linarith

/-- Eq. (8): `A n = (−1)^{n+1} (4/π) I n` for `n ≥ 1`. -/
theorem A_eq_sign_integral (n : ℕ) (hn : 1 ≤ n) :
    A n = (-1 : ℝ) ^ (n + 1) * (4 / π) * I n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- Step 1: the sine-integral difference is the integral of sinc over [(n−½)π, (n+½)π].
  have hdiff : Si (((n : ℝ) + 1 / 2) * π) - Si (((n : ℝ) - 1 / 2) * π) =
      ∫ x in (((n : ℝ) - 1 / 2) * π)..(((n : ℝ) + 1 / 2) * π), sinc x := by
    unfold Si
    rw [intervalIntegral.integral_interval_sub_left (intervalIntegrable_sinc _ _)
      (intervalIntegrable_sinc _ _)]
  -- Step 2: the shift x = nπ + s.
  have hshift : (∫ x in (((n : ℝ) - 1 / 2) * π)..(((n : ℝ) + 1 / 2) * π), sinc x) =
      ∫ s in (-(π / 2))..(π / 2), sinc (n * π + s) := by
    rw [intervalIntegral.integral_comp_add_left]
    congr 1 <;> ring
  -- Step 3: sinc(nπ + s) = (−1)^n sin s/(nπ + s) on the interval.
  have hsign : (∫ s in (-(π / 2))..(π / 2), sinc (n * π + s)) =
      (-1 : ℝ) ^ n * ∫ s in (-(π / 2))..(π / 2), Real.sin s / (n * π + s) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun s hs => sinc_shift n hn hs)
  -- Step 4: pairing s and −s.
  have hcont : ContinuousOn (fun s : ℝ => Real.sin s / (n * π + s)) (uIcc (-(π / 2)) (π / 2)) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs
    rw [uIcc_of_le (by linarith [pi_pos])] at hs
    have : 0 < (n : ℝ) * π + s := by nlinarith [pi_pos, hs.1]
    exact this.ne'
  have hpair : (∫ s in (-(π / 2))..(π / 2), Real.sin s / (n * π + s)) = -2 * I n := by
    have hi1 : IntervalIntegrable (fun s : ℝ => Real.sin s / (n * π + s)) MeasureTheory.volume
        (-(π / 2)) 0 :=
      (hcont.mono (uIcc_subset_uIcc_left (by
        rw [uIcc_of_le (by linarith [pi_pos])]; constructor <;> linarith [pi_pos]))).intervalIntegrable
    have hi2 : IntervalIntegrable (fun s : ℝ => Real.sin s / (n * π + s)) MeasureTheory.volume
        0 (π / 2) :=
      (hcont.mono (uIcc_subset_uIcc_right (by
        rw [uIcc_of_le (by linarith [pi_pos])]; constructor <;> linarith [pi_pos]))).intervalIntegrable
    rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
    have hneg := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π / 2)
      (fun s : ℝ => Real.sin s / (n * π + s))
    simp only [neg_zero] at hneg
    rw [← hneg, ← intervalIntegral.integral_add]
    · rw [I, ← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr (fun s hs => by
        rw [add_comm]; exact pair_identity n hn hs)
    · have : ContinuousOn (fun s : ℝ => Real.sin (-s) / (n * π + -s)) (uIcc 0 (π / 2)) := by
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro s hs
        rw [uIcc_of_le (by linarith [pi_pos])] at hs
        have : 0 < (n : ℝ) * π + -s := by nlinarith [pi_pos, hs.2]
        exact this.ne'
      exact this.intervalIntegrable
    · exact hi2
  rw [A_eq_Si, hdiff, hshift, hsign, hpair]
  ring

/-! ### Positivity, bounds and monotonicity of `I n` -/

lemma integral_s_sin : (∫ s in (0 : ℝ)..(π / 2), s * Real.sin s) = 1 := by
  have h : ∀ x ∈ uIcc (0 : ℝ) (π / 2),
      HasDerivAt (fun s => Real.sin s - s * Real.cos s) (x * Real.sin x) x := by
    intro x _
    have h1 := Real.hasDerivAt_sin x
    have h2 : HasDerivAt (fun s => s * Real.cos s) (1 * Real.cos x + x * -Real.sin x) x :=
      (hasDerivAt_id' x).mul (Real.hasDerivAt_cos x)
    convert h1.sub h2 using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((continuous_id.mul Real.continuous_sin).intervalIntegrable _ _)]
  simp [Real.sin_pi_div_two, Real.cos_pi_div_two]

lemma s_sin_nonneg {s : ℝ} (hs : s ∈ Icc 0 (π / 2)) : 0 ≤ s * Real.sin s :=
  mul_nonneg hs.1 (Real.sin_nonneg_of_nonneg_of_le_pi hs.1 (by linarith [hs.2, pi_pos]))

/-- The lower bound of Eq. (9) for `I n`: `1/(n²π²) < I n`. -/
lemma I_gt (n : ℕ) (hn : 1 ≤ n) : 1 / ((n : ℝ) ^ 2 * π ^ 2) < I n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hP : 0 < (n : ℝ) ^ 2 * π ^ 2 := by positivity
  have hlhs : 1 / ((n : ℝ) ^ 2 * π ^ 2) =
      ∫ s in (0 : ℝ)..(π / 2), s * Real.sin s / ((n : ℝ) ^ 2 * π ^ 2) := by
    rw [intervalIntegral.integral_div, integral_s_sin]
  rw [hlhs, I]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith [pi_pos]) (by fun_prop) (continuousOn_kernel n hn)
  · intro s hs
    have hs' : s ∈ Icc 0 (π / 2) := Ioc_subset_Icc_self hs
    have hden : 0 < (n : ℝ) ^ 2 * π ^ 2 - s ^ 2 := by nlinarith [den_pos hn hs', s_sq_le hs', pi_pos]
    exact div_le_div_of_nonneg_left (s_sin_nonneg hs') hden (by nlinarith [hs'.1])
  · refine ⟨π / 2, ⟨by linarith [pi_pos], le_rfl⟩, ?_⟩
    rw [Real.sin_pi_div_two, mul_one]
    have hden : 0 < (n : ℝ) ^ 2 * π ^ 2 - (π / 2) ^ 2 := by
      have := den_pos hn (⟨by linarith [pi_pos], le_rfl⟩ : π / 2 ∈ Icc 0 (π / 2)); nlinarith [pi_pos]
    exact div_lt_div_of_pos_left (by linarith [pi_pos]) hden (by nlinarith [pi_pos])

/-- The upper bound of Eq. (9) for `I n`: `I n < 1/(π²(n² − ¼))`. -/
lemma I_lt (n : ℕ) (hn : 1 ≤ n) : I n < 1 / (π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ : 0 < π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4) := by
    have : (0 : ℝ) < (n : ℝ) ^ 2 - 1 / 4 := by nlinarith
    positivity
  have hrhs : 1 / (π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4)) =
      ∫ s in (0 : ℝ)..(π / 2), s * Real.sin s / (π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4)) := by
    rw [intervalIntegral.integral_div, integral_s_sin]
  rw [hrhs, I]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith [pi_pos]) (continuousOn_kernel n hn) (by fun_prop)
  · intro s hs
    have hs' : s ∈ Icc 0 (π / 2) := Ioc_subset_Icc_self hs
    have hle : π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4) ≤ (n : ℝ) ^ 2 * π ^ 2 - s ^ 2 := by
      nlinarith [den_pos hn hs', s_sq_le hs', pi_pos]
    exact div_le_div_of_nonneg_left (s_sin_nonneg hs') hQ hle
  · refine ⟨π / 4, ⟨by linarith [pi_pos], by linarith [pi_pos]⟩, ?_⟩
    have hsin : 0 < Real.sin (π / 4) := Real.sin_pos_of_pos_of_lt_pi (by linarith [pi_pos])
      (by linarith [pi_pos])
    have hlt : π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4) < (n : ℝ) ^ 2 * π ^ 2 - (π / 4) ^ 2 := by
      nlinarith [pi_pos]
    exact div_lt_div_of_pos_left (mul_pos (by linarith [pi_pos]) hsin) hQ hlt

lemma I_pos (n : ℕ) (hn : 1 ≤ n) : 0 < I n :=
  lt_trans (by positivity) (I_gt n hn)

/-- Strict decrease of `I n` (hence of `|A n|`). -/
lemma I_succ_lt (n : ℕ) (hn : 1 ≤ n) : I (n + 1) < I n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [I, I]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by linarith [pi_pos]) (continuousOn_kernel (n + 1) (by omega)) (continuousOn_kernel n hn)
  · intro s hs
    have hs' : s ∈ Icc 0 (π / 2) := Ioc_subset_Icc_self hs
    have hden : 0 < (n : ℝ) ^ 2 * π ^ 2 - s ^ 2 := by nlinarith [den_pos hn hs', s_sq_le hs', pi_pos]
    have hle : (n : ℝ) ^ 2 * π ^ 2 - s ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * π ^ 2 - s ^ 2 := by
      push_cast; nlinarith [pi_pos]
    exact div_le_div_of_nonneg_left (s_sin_nonneg hs') hden hle
  · refine ⟨π / 2, ⟨by linarith [pi_pos], le_rfl⟩, ?_⟩
    rw [Real.sin_pi_div_two, mul_one]
    have hden : 0 < (n : ℝ) ^ 2 * π ^ 2 - (π / 2) ^ 2 := by
      have := den_pos hn (⟨by linarith [pi_pos], le_rfl⟩ : π / 2 ∈ Icc 0 (π / 2)); nlinarith [pi_pos]
    have hlt : (n : ℝ) ^ 2 * π ^ 2 - (π / 2) ^ 2 < ((n + 1 : ℕ) : ℝ) ^ 2 * π ^ 2 - (π / 2) ^ 2 := by
      push_cast; nlinarith [pi_pos]
    exact div_lt_div_of_pos_left (by linarith [pi_pos]) hden hlt

/-! ### Proposition 3.1: signs, monotonicity, bounds, summability -/

theorem abs_A (n : ℕ) (hn : 1 ≤ n) : |A n| = (4 / π) * I n := by
  rw [A_eq_sign_integral n hn, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 4 / π), abs_of_pos (I_pos n hn)]

/-- `sgn A n = (−1)^{n+1}`: `A n = (−1)^{n+1} |A n|` with `|A n| > 0`. -/
theorem A_sign (n : ℕ) (hn : 1 ≤ n) : A n = (-1 : ℝ) ^ (n + 1) * |A n| ∧ 0 < |A n| := by
  refine ⟨?_, ?_⟩
  · rw [abs_A n hn, A_eq_sign_integral n hn]; ring
  · rw [abs_A n hn]; exact mul_pos (by positivity) (I_pos n hn)

theorem abs_A_strictAnti (n : ℕ) (hn : 1 ≤ n) : |A (n + 1)| < |A n| := by
  rw [abs_A n hn, abs_A (n + 1) (by omega)]
  exact mul_lt_mul_of_pos_left (I_succ_lt n hn) (by positivity)

/-- Eq. (9): `4/(π³ n²) < |A n| < 4/(π³ (n² − ¼))`. -/
theorem abs_A_bounds (n : ℕ) (hn : 1 ≤ n) :
    4 / (π ^ 3 * (n : ℝ) ^ 2) < |A n| ∧ |A n| < 4 / (π ^ 3 * ((n : ℝ) ^ 2 - 1 / 4)) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4 : (0 : ℝ) < 4 / π := by positivity
  rw [abs_A n hn]
  constructor
  · have := mul_lt_mul_of_pos_left (I_gt n hn) h4
    calc 4 / (π ^ 3 * (n : ℝ) ^ 2) = 4 / π * (1 / ((n : ℝ) ^ 2 * π ^ 2)) := by
          field_simp
      _ < _ := this
  · have := mul_lt_mul_of_pos_left (I_lt n hn) h4
    calc 4 / π * I n < 4 / π * (1 / (π ^ 2 * ((n : ℝ) ^ 2 - 1 / 4))) := this
      _ = 4 / (π ^ 3 * ((n : ℝ) ^ 2 - 1 / 4)) := by
          have : (0 : ℝ) < (n : ℝ) ^ 2 - 1 / 4 := by nlinarith
          field_simp

/-- A clean majorant: `|A n| ≤ (16/(3π³)) / n²` for `n ≥ 1`. -/
lemma abs_A_le (n : ℕ) (hn : 1 ≤ n) : |A n| ≤ 16 / (3 * π ^ 3) * (1 / (n : ℝ) ^ 2) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb := (abs_A_bounds n hn).2
  have hq : (0 : ℝ) < (n : ℝ) ^ 2 - 1 / 4 := by nlinarith
  have : 4 / (π ^ 3 * ((n : ℝ) ^ 2 - 1 / 4)) ≤ 16 / (3 * π ^ 3) * (1 / (n : ℝ) ^ 2) := by
    rw [div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [pi_pos, pow_pos pi_pos 3]
  linarith

/-- Absolute summability of the cosine coefficients. -/
theorem summable_abs_A : Summable (fun n => |A n|) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun n => abs_A_le (n + 1) (by omega)) ?_
  refine (Summable.mul_left _ ?_)
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
  rw [← summable_nat_add_iff 1] at h
  simpa using h

/-- Eq. (10) with an explicit constant: `|A n − (−1)^{n+1} 4/(π³n²)| ≤ (4/(3π³)) / n⁴`. -/
theorem A_asymptotic (n : ℕ) (hn : 1 ≤ n) :
    |A n - (-1 : ℝ) ^ (n + 1) * (4 / (π ^ 3 * (n : ℝ) ^ 2))| ≤
      4 / (3 * π ^ 3) * (1 / (n : ℝ) ^ 4) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨hs, _⟩ := A_sign n hn
  obtain ⟨hlo, hhi⟩ := abs_A_bounds n hn
  have hq : (0 : ℝ) < (n : ℝ) ^ 2 - 1 / 4 := by nlinarith
  have hsq : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have habs1 : |(-1 : ℝ) ^ (n + 1)| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have key : A n - (-1 : ℝ) ^ (n + 1) * (4 / (π ^ 3 * (n : ℝ) ^ 2)) =
      (-1 : ℝ) ^ (n + 1) * (|A n| - 4 / (π ^ 3 * (n : ℝ) ^ 2)) := by
    conv_lhs => rw [hs]
    ring
  rw [key, abs_mul, habs1, one_mul, abs_of_pos (by linarith)]
  have : 4 / (π ^ 3 * ((n : ℝ) ^ 2 - 1 / 4)) - 4 / (π ^ 3 * (n : ℝ) ^ 2) ≤
      4 / (3 * π ^ 3) * (1 / (n : ℝ) ^ 4) := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [pi_pos, pow_pos pi_pos 3, pow_pos pi_pos 6]
  linarith

end EulerianCert.FourierModes
