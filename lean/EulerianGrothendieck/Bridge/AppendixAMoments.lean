import Bridge.AppendixA
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Appendix A (continued): even moments of the arcsine, semicircle and Gaussian laws

Manuscript V173, eqs. (296)–(298).

* (296) `(1/π) ∫_{-2}^{2} x^{2k}/√(4-x²) dx = C(2k,k)`;
* (297) `(1/(2π)) ∫_{-2}^{2} x^{2k} √(4-x²) dx = C_k`;
* (298) `∫_ℝ x^{2k} e^{-x²/2}/√(2π) dx = (2k-1)!!`.
The first two reduce through `x = 2 sin θ` to Wallis integrals.
-/

open Real MeasureTheory Set intervalIntegral
open scoped Nat

namespace EulerianBridge.AppendixA

/-- Eq. (298): Gaussian moments. -/
theorem gaussian_moment (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k) * exp (-x ^ 2 / 2) / Real.sqrt (2 * π) = ((2 * k - 1 : ℕ)‼ : ℝ) := by
  -- even integrand: ∫_ℝ = 2 ∫_{Ioi 0}
  have heven : ∫ x : ℝ, x ^ (2 * k) * exp (-x ^ 2 / 2) =
      2 * ∫ x in Ioi (0:ℝ), x ^ (2 * k) * exp (-x ^ 2 / 2) := by
    have := integral_comp_abs (f := fun x : ℝ => x ^ (2 * k) * exp (-x ^ 2 / 2))
    simp only [pow_mul, sq_abs] at this
    simpa [pow_mul] using this
  have hhalf : ∫ x in Ioi (0:ℝ), x ^ (2 * k) * exp (-x ^ 2 / 2) =
      (1 / 2 : ℝ) ^ (-((2 * k : ℝ) + 1) / 2) * (1 / 2) * Gamma (((2 * k : ℝ) + 1) / 2) := by
    have := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := 2 * k) (b := 1 / 2) (by norm_num)
      (by have : (0:ℝ) ≤ k := k.cast_nonneg; linarith) (by norm_num)
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : 0 ≤ x := le_of_lt hx
    rw [show (2 * (k:ℝ)) = ((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, Real.rpow_two]
    ring_nf
  rw [MeasureTheory.integral_div, heven, hhalf]
  have hG : Gamma (((2 * k : ℝ) + 1) / 2) = ((2 * k - 1 : ℕ)‼ : ℝ) * √π / 2 ^ k := by
    rw [show ((2 * k : ℝ) + 1) / 2 = (k:ℝ) + 1 / 2 by ring, Real.Gamma_nat_add_half]
  rw [hG]
  have hpow : (1 / 2 : ℝ) ^ (-((2 * k : ℝ) + 1) / 2) = 2 ^ (k:ℝ) * √2 := by
    rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num),
      show -(-((2 * k : ℝ) + 1) / 2) = (k:ℝ) + 1 / 2 by ring, Real.rpow_add (by norm_num),
      Real.sqrt_eq_rpow]
  rw [hpow, Real.rpow_natCast, Real.sqrt_mul (by norm_num) π]
  have h2 : (0:ℝ) < √2 := by positivity
  have hp : (0:ℝ) < √π := Real.sqrt_pos.mpr pi_pos
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  field_simp

/-! ## Arcsine and semicircle laws -/

/-- The open half-period `(-π/2, π/2)`. -/
local notation "Θ" => Ioo (-(π / 2)) (π / 2)

theorem sin_mem_Ioo {θ : ℝ} (hθ : θ ∈ Θ) : Real.sin θ ∈ Ioo (-1) 1 := by
  have hm := Real.strictMonoOn_sin
  have hI : θ ∈ Icc (-(π / 2)) (π / 2) := Ioo_subset_Icc_self hθ
  have hl : -(π / 2) ∈ Icc (-(π / 2)) (π / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hr : π / 2 ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [Real.pi_pos], le_rfl⟩
  constructor
  · have := hm hl hI hθ.1; rwa [Real.sin_neg, Real.sin_pi_div_two] at this
  · have := hm hI hr hθ.2; rwa [Real.sin_pi_div_two] at this

theorem image_two_sin : (fun θ : ℝ => 2 * Real.sin θ) '' Θ = Ioo (-2) 2 := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    have := sin_mem_Ioo hθ
    constructor <;> linarith [this.1, this.2]
  · intro hx
    refine ⟨Real.arcsin (x / 2), ⟨Real.neg_pi_div_two_lt_arcsin.mpr (by linarith [hx.1]),
      Real.arcsin_lt_pi_div_two.mpr (by linarith [hx.2])⟩, ?_⟩
    simp only
    rw [Real.sin_arcsin (by linarith [hx.1]) (by linarith [hx.2])]; ring

theorem injOn_two_sin : InjOn (fun θ : ℝ => 2 * Real.sin θ) Θ := by
  intro a ha b hb h
  apply Real.injOn_sin (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb)
  simpa using h

theorem cos_pos_of_mem {θ : ℝ} (hθ : θ ∈ Θ) : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo hθ

theorem sqrt_four_sub {θ : ℝ} (hθ : θ ∈ Θ) : Real.sqrt (4 - (2 * Real.sin θ) ^ 2) = 2 * Real.cos θ := by
  have hc := cos_pos_of_mem hθ
  rw [show 4 - (2 * Real.sin θ) ^ 2 = (2 * Real.cos θ) ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq (by positivity)

/-- The change of variables `x = 2 sin θ` on `(-π/2, π/2)`. -/
theorem change_two_sin (g : ℝ → ℝ) :
    ∫ x in (-2:ℝ)..2, g x = ∫ θ in Θ, |2 * Real.cos θ| * g (2 * Real.sin θ) := by
  rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo, ← image_two_sin,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun θ _ => ((Real.hasDerivAt_sin θ).const_mul 2).hasDerivWithinAt) injOn_two_sin]
  simp only [smul_eq_mul]

theorem setIntegral_Θ (h : ℝ → ℝ) : ∫ θ in Θ, h θ = ∫ θ in (-(π / 2))..(π / 2), h θ := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem prod_wallis (k : ℕ) :
    ∏ i ∈ Finset.range k, (2 * (i:ℝ) + 1) / (2 * i + 2) = (Nat.centralBinom k : ℝ) / 4 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h := Nat.succ_mul_centralBinom_succ n
    have h' : ((n:ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n := by
      exact_mod_cast h
    have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
    rw [show (Nat.centralBinom (n + 1) : ℝ) = 2 * (2 * n + 1) * Nat.centralBinom n / (n + 1) by
      field_simp; linarith [h'], pow_succ]
    field_simp
    ring

/-- Wallis over a half-period: `∫_{-π/2}^{π/2} sin^{2k} = π C(2k,k)/4^k`. -/
theorem wallis (k : ℕ) :
    ∫ θ in (-(π / 2))..(π / 2), Real.sin θ ^ (2 * k) = π * (Nat.centralBinom k : ℝ) / 4 ^ k := by
  have hper : Function.Periodic (fun θ : ℝ => Real.sin θ ^ (2 * k)) π := by
    intro θ; simp only [Real.sin_add_pi, pow_mul, neg_sq]
  have := hper.intervalIntegral_add_eq (-(π / 2)) 0
  rw [show -(π / 2) + π = π / 2 by ring, zero_add] at this
  rw [this, integral_sin_pow_even, prod_wallis, mul_div_assoc]

/-- `x = 2 sin θ` turns the arcsine moment into a Wallis integral. -/
theorem arcsine_subst (k : ℕ) :
    ∫ x in (-2:ℝ)..2, x ^ (2 * k) / Real.sqrt (4 - x ^ 2) =
      4 ^ k * ∫ θ in (-(π / 2))..(π / 2), Real.sin θ ^ (2 * k) := by
  rw [change_two_sin, ← intervalIntegral.integral_const_mul, ← setIntegral_Θ]
  refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
  have hc := cos_pos_of_mem hθ
  rw [sqrt_four_sub hθ, abs_of_pos (by positivity), mul_pow, pow_mul, pow_mul]
  field_simp
  norm_num
  ring

/-- Eq. (296): `(1/π) ∫_{-2}^{2} x^{2k}/√(4-x²) dx = C(2k,k)`. -/
theorem arcsine_moment (k : ℕ) :
    (1 / π) * ∫ x in (-2:ℝ)..2, x ^ (2 * k) / Real.sqrt (4 - x ^ 2) = (Nat.centralBinom k : ℝ) := by
  rw [arcsine_subst, wallis]
  have := Real.pi_pos
  field_simp

/-- Eq. (297): `(1/(2π)) ∫_{-2}^{2} x^{2k} √(4-x²) dx = C_k`. -/
theorem semicircle_moment (k : ℕ) :
    (1 / (2 * π)) * ∫ x in (-2:ℝ)..2, x ^ (2 * k) * Real.sqrt (4 - x ^ 2) = (catalan k : ℝ) := by
  have hsub : ∫ x in (-2:ℝ)..2, x ^ (2 * k) * Real.sqrt (4 - x ^ 2) =
      4 ^ (k + 1) * ((∫ θ in (-(π / 2))..(π / 2), Real.sin θ ^ (2 * k)) -
        ∫ θ in (-(π / 2))..(π / 2), Real.sin θ ^ (2 * (k + 1))) := by
    rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul,
      change_two_sin, ← setIntegral_Θ]
    refine setIntegral_congr_fun measurableSet_Ioo (fun θ hθ => ?_)
    have hc := cos_pos_of_mem hθ
    rw [sqrt_four_sub hθ, abs_of_pos (by positivity), show 2 * (k + 1) = 2 * k + 2 by ring, pow_add,
      mul_pow, show (2:ℝ) ^ (2 * k) = 4 ^ k by rw [pow_mul]; norm_num]
    have hsc : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by nlinarith [Real.sin_sq_add_cos_sq θ]
    linear_combination (4 * 4 ^ k * Real.sin θ ^ (2 * k)) * hsc
  rw [hsub, wallis, wallis]
  have hcat := succ_mul_catalan_eq_centralBinom k
  have hcat' : ((k:ℝ) + 1) * (catalan k : ℝ) = Nat.centralBinom k := by exact_mod_cast hcat
  have h := Nat.succ_mul_centralBinom_succ k
  have h' : ((k:ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) = 2 * (2 * k + 1) * Nat.centralBinom k := by
    exact_mod_cast h
  have hk : ((k:ℝ) + 1) ≠ 0 := by positivity
  have hp := Real.pi_pos
  rw [show (Nat.centralBinom (k + 1) : ℝ) = 2 * (2 * k + 1) * Nat.centralBinom k / (k + 1) by
      field_simp; linarith [h'],
    show (catalan k : ℝ) = Nat.centralBinom k / (k + 1) by field_simp; linarith [hcat']]
  field_simp
  ring

end EulerianBridge.AppendixA
