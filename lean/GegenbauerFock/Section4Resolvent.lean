import GegenbauerFock.Manuscript13Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Manuscript 13, Section 4: the Eulerian profile and the free Laplacian spectral density

All special functions are those of Section 3 (`GegenbauerFock.Manuscript13`):
`ν λ` is the ultraspherical probability measure, `Φ λ z = ∫ e^{izu} dν_λ(u)`, and
`besselJ λ t = (t/2)^λ ∑ (-1)ⁿ/(n! Γ(n+λ+1)) (t²/4)ⁿ` is the series Bessel function.

* **Theorem 4.1** (`theorem_4_1`, `theorem_4_1_extension`, `theorem_4_1_diagonal`):
  `Φ_{(d-2)/2}(kρ) = 4Γ(d/2) √((4π/k²)^{d-2}) Im G^out_{d,k}(ρ)` for `d ≥ 3`, `k, ρ > 0`,
  with `G^out` defined literally by `eq:outgoing-resolvent`–`eq:hankel-first-kind`, and the continuous extension to `ρ = 0`.
* **Corollary 4.2** (`corollary_4_2`, `corollary_4_2_origin`).
* **Proposition 4.3** (`proposition_4_3`, `proposition_4_3_origin`, `nuEndpoint_moment_limit`).
* **Proposition 4.4** (`proposition_4_4`), from the sphere average `eq:sphere-average` (`sphere_average`).
* **Table 1** (`table_1`, `table_1_endpoints`).

Classical inputs that Mathlib lacks enter only as explicit data or named hypotheses:
* the Neumann function is an arbitrary *real-valued* function `Y : ℝ → ℝ → ℝ` (order, argument);
  its reality is encoded by its type, and nothing else about it is used in Theorem 4.1;
* the closed forms `Y_{1/2}(t) = -√(2/(πt)) cos t` and `Y_{-1/2}(t) = √(2/(πt)) sin t` are
  hypotheses of `Gout_three` and `Gout_one` only (the closed forms of `J_{±1/2}` are proved);
* the zonal marginal law of the uniform sphere measure (`ZonalMarginal`) is a hypothesis of the
  sphere average and of Proposition 4.4.
-/

noncomputable section

open Real MeasureTheory Set Filter Topology Complex
open scoped ComplexConjugate

namespace GegenbauerFock.Section4Resolvent

open GegenbauerFock.Manuscript13 (ν Φ besselJ rE isProbability Phi_bessel Phi_zero rE_eq_Phi
  pochhammer_half)

/-! ## Definitions: Hankel function, outgoing kernel, coefficient -/

/-- The Hankel function of the first kind, `eq:hankel-first-kind`: `H^{(1)}_ν = J_ν + i Y_ν`, with the series
Bessel function `J_ν` of Section 3 and a real-valued Neumann function `Y` (a classical input). -/
def hankel1 (Y : ℝ → ℝ → ℝ) (o t : ℝ) : ℂ := (besselJ o t : ℂ) + I * (Y o t : ℂ)

/-- The outgoing Helmholtz kernel, `eq:outgoing-resolvent`:
`G^out_{d,k}(ρ) = (i/4) (k/(2πρ))^{(d-2)/2} H^{(1)}_{(d-2)/2}(kρ)`. -/
def Gout (Y : ℝ → ℝ → ℝ) (d : ℕ) (k ρ : ℝ) : ℂ :=
  I / 4 * (((k / (2 * π * ρ)) ^ (((d : ℝ) - 2) / 2) : ℝ) : ℂ) *
    hankel1 Y (((d : ℝ) - 2) / 2) (k * ρ)

/-- The coefficient of Theorem 4.1 and Table 1: `A_d(k) = 4Γ(d/2) √((4π/k²)^{d-2})`. -/
def A (d : ℕ) (k : ℝ) : ℝ := 4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2))

/-- The same coefficient written with a real power, `eq:dimensional-factor-proof`: `4Γ(d/2) (4π/k²)^{(d-2)/2}`. -/
def Arpow (d : ℕ) (k : ℝ) : ℝ := 4 * Real.Gamma ((d : ℝ) / 2) * (4 * π / k ^ 2) ^ (((d : ℝ) - 2) / 2)

/-! ## Elementary lemmas -/

theorem sqrt_mul_sqrt_eq {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : a * b = c ^ 2) :
    Real.sqrt a * Real.sqrt b = c := by
  rw [← Real.sqrt_mul ha, h, Real.sqrt_sq hc]

theorem sqrt_four_pi_div {k : ℝ} (hk : 0 < k) :
    Real.sqrt (4 * π / k ^ 2) = 2 * Real.sqrt π / k := by
  have e : 4 * π / k ^ 2 = (2 * Real.sqrt π / k) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]; ring
  rw [e]
  exact Real.sqrt_sq (by positivity)

theorem rpow_neg_half {x : ℝ} (hx : 0 < x) : x ^ (-1 / 2 : ℝ) = Real.sqrt x⁻¹ := by
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow,
    Real.sqrt_inv]

/-- `Γ(n + 1/2) = √π (1/2)_n`. -/
theorem Gamma_nat_add_half (n : ℕ) :
    Real.Gamma (n + 1 / 2) = Real.sqrt π * (ascPochhammer ℝ n).eval (1 / 2) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq, ascPochhammer_zero, Polynomial.eval_one,
      mul_one]
  | succ n ih =>
    rw [ascPochhammer_succ_eval, show ((n + 1 : ℕ) : ℝ) + 1 / 2 = (n + 1 / 2) + 1 by push_cast; ring,
      Real.Gamma_add_one (by positivity), ih]
    ring

theorem mul_conj_eq (z : ℂ) : z * conj z = ((Complex.normSq z : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.normSq_apply]
    ring
  · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_im]
    ring

theorem norm_cexp_I_mul (a b : ℝ) : ‖cexp (I * (a : ℂ) * (b : ℂ))‖ = 1 := by
  rw [show I * (a : ℂ) * (b : ℂ) = ((a * b : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (a * b)

/-! ## Continuity and reality of `Φ_λ` on the real axis -/

theorem continuous_Phi_ofReal {l : ℝ} (hl : -1 / 2 < l) :
    Continuous fun t : ℝ => Φ l (t : ℂ) := by
  haveI := isProbability hl
  show Continuous fun t : ℝ => ∫ u, cexp (I * (t : ℂ) * (u : ℂ)) ∂(ν l)
  refine continuous_of_dominated (bound := fun _ => (1 : ℝ)) (fun t => ?_) (fun t => ?_)
    (integrable_const 1) (ae_of_all _ fun u => ?_)
  · exact (by fun_prop : Continuous fun u : ℝ => cexp (I * (t : ℂ) * (u : ℂ))).aestronglyMeasurable
  · exact ae_of_all _ fun u => (norm_cexp_I_mul t u).le
  · fun_prop

theorem Phi_ofReal_im {l : ℝ} (hl : -1 / 2 < l) {t : ℝ} (ht : 0 ≤ t) : (Φ l (t : ℂ)).im = 0 := by
  rcases ht.lt_or_eq with h | h
  · rw [Phi_bessel hl h, Complex.ofReal_im]
  · rw [← h, Complex.ofReal_zero, Phi_zero hl, Complex.one_im]

/-! ## Theorem 4.1 -/

/-- `eq:resolvent-imaginary`: `Im G^out_{d,k}(ρ) = (1/4) (k/(2πρ))^{(d-2)/2} J_{(d-2)/2}(kρ)`; only the reality of
`J` and `Y` is used. -/
theorem Gout_im (Y : ℝ → ℝ → ℝ) (d : ℕ) (k ρ : ℝ) :
    (Gout Y d k ρ).im =
      (k / (2 * π * ρ)) ^ (((d : ℝ) - 2) / 2) * besselJ (((d : ℝ) - 2) / 2) (k * ρ) / 4 := by
  unfold Gout hankel1
  generalize (k / (2 * π * ρ)) ^ (((d : ℝ) - 2) / 2) = c
  generalize besselJ (((d : ℝ) - 2) / 2) (k * ρ) = J
  generalize Y (((d : ℝ) - 2) / 2) (k * ρ) = y
  have h : I / 4 * (c : ℂ) * ((J : ℂ) + I * (y : ℂ)) =
      ((-(c * y) / 4 : ℝ) : ℂ) + ((c * J / 4 : ℝ) : ℂ) * I := by
    push_cast
    linear_combination ((c : ℂ) * (y : ℂ) / 4) * I_sq
  rw [h]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

/-- `eq:dimensional-factor-proof`: the square-root and real-power forms of the coefficient agree for `d ≥ 2`. -/
theorem A_eq_Arpow {d : ℕ} (hd : 2 ≤ d) (k : ℝ) : A d k = Arpow d k := by
  unfold A Arpow
  have hx : 0 ≤ 4 * π / k ^ 2 := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx, Nat.cast_sub hd]
  congr 2
  push_cast
  ring

/-- **Theorem 4.1**, `eq:resolvent-dimensional`: the exact dimensional resolvent–Gegenbauer identity. -/
theorem theorem_4_1 (Y : ℝ → ℝ → ℝ) {d : ℕ} (hd : 3 ≤ d) {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    Φ (((d : ℝ) - 2) / 2) ((k * ρ : ℝ) : ℂ) =
      ((4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)) *
        (Gout Y d k ρ).im : ℝ) : ℂ) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hl : (-1 / 2 : ℝ) < ((d : ℝ) - 2) / 2 := by linarith
  have ht : 0 < k * ρ := mul_pos hk hρ
  have hx : 0 ≤ 4 * π / k ^ 2 := by positivity
  have hA : 4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)) =
      4 * Real.Gamma ((d : ℝ) / 2) * (4 * π / k ^ 2) ^ (((d : ℝ) - 2) / 2) :=
    A_eq_Arpow (by omega) k
  rw [Phi_bessel hl ht, Gout_im, hA]
  congr 1
  have hprod : (4 * π / k ^ 2) ^ (((d : ℝ) - 2) / 2) * (k / (2 * π * ρ)) ^ (((d : ℝ) - 2) / 2) =
      (2 / (k * ρ)) ^ (((d : ℝ) - 2) / 2) := by
    rw [← Real.mul_rpow hx (by positivity)]
    congr 1
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [show ((d : ℝ) - 2) / 2 + 1 = (d : ℝ) / 2 by ring, ← hprod]
  ring

/-- **Theorem 4.1**, continuous extension: the right-hand side tends to `1` as `ρ ↓ 0`. -/
theorem theorem_4_1_extension (Y : ℝ → ℝ → ℝ) {d : ℕ} (hd : 3 ≤ d) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun ρ : ℝ => 4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)) *
      (Gout Y d k ρ).im) (𝓝[>] 0) (𝓝 1) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hl : (-1 / 2 : ℝ) < ((d : ℝ) - 2) / 2 := by linarith
  have hc : Continuous fun ρ : ℝ => (Φ (((d : ℝ) - 2) / 2) ((k * ρ : ℝ) : ℂ)).re :=
    Complex.continuous_re.comp ((continuous_Phi_ofReal hl).comp (continuous_const.mul continuous_id))
  have h0 : Tendsto (fun ρ : ℝ => (Φ (((d : ℝ) - 2) / 2) ((k * ρ : ℝ) : ℂ)).re) (𝓝[>] 0) (𝓝 1) := by
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [mul_zero, Complex.ofReal_zero, Phi_zero hl, Complex.one_re] at h
    exact h
  refine h0.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
  rw [theorem_4_1 Y hd hk hρ, Complex.ofReal_re]

/-- **Theorem 4.1**, `eq:resolvent-diagonal`: the diagonal value of `Im G^out_{d,k}`. -/
theorem theorem_4_1_diagonal (Y : ℝ → ℝ → ℝ) {d : ℕ} (hd : 3 ≤ d) {k : ℝ} (hk : 0 < k) :
    Tendsto (fun ρ : ℝ => (Gout Y d k ρ).im) (𝓝[>] 0)
      (𝓝 (1 / (4 * Real.Gamma ((d : ℝ) / 2)) * Real.sqrt ((k ^ 2 / (4 * π)) ^ (d - 2)))) := by
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hS : 0 < Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)) := Real.sqrt_pos.mpr (by positivity)
  have hApos : 0 < 4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)) := by
    positivity
  have h := (theorem_4_1_extension Y hd hk).const_mul
    (4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)))⁻¹
  have e : 1 / (4 * Real.Gamma ((d : ℝ) / 2)) * Real.sqrt ((k ^ 2 / (4 * π)) ^ (d - 2)) =
      (4 * Real.Gamma ((d : ℝ) / 2) * Real.sqrt ((4 * π / k ^ 2) ^ (d - 2)))⁻¹ * 1 := by
    rw [show k ^ 2 / (4 * π) = (4 * π / k ^ 2)⁻¹ from (inv_div _ _).symm, inv_pow, Real.sqrt_inv]
    ring
  rw [e]
  refine h.congr fun ρ => ?_
  rw [← mul_assoc, inv_mul_cancel₀ hApos.ne', one_mul]

/-! ## The half-integer Bessel functions -/

/-- `r_E(ρ) = sin(ρ/2)/(ρ/2)` for real `ρ ≠ 0`. -/
theorem rE_ofReal {ρ : ℝ} (hρ : ρ ≠ 0) :
    rE (ρ : ℂ) = ((Real.sin (ρ / 2) / (ρ / 2) : ℝ) : ℂ) := by
  have hc : I * (ρ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr hρ)
  have h2 : (ρ : ℂ) / 2 ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hρ) two_ne_zero
  rw [rE, integral_exp_mul_complex hc]
  rw [show I * (ρ : ℂ) * ((1 / 2 : ℝ) : ℂ) = ((ρ / 2 : ℝ) : ℂ) * I by push_cast; ring,
    show I * (ρ : ℂ) * ((-1 / 2 : ℝ) : ℂ) = -((ρ / 2 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  rw [div_eq_div_iff hc h2]
  ring

/-- `Φ_{1/2}(t) = sin t / t` for real `t ≠ 0`. -/
theorem Phi_half_ofReal {t : ℝ} (ht : t ≠ 0) : Φ (1 / 2) (t : ℂ) = ((Real.sin t / t : ℝ) : ℂ) := by
  have h := rE_eq_Phi ((2 * t : ℝ) : ℂ)
  rw [rE_ofReal (mul_ne_zero two_ne_zero ht),
    show ((2 * t : ℝ) : ℂ) / 2 = (t : ℂ) by push_cast; ring, show 2 * t / 2 = t by ring] at h
  exact h.symm

/-- The closed form `J_{1/2}(t) = √(2/(πt)) sin t`, proved from the series. -/
theorem besselJ_half {t : ℝ} (ht : 0 < t) :
    besselJ (1 / 2) t = Real.sqrt (2 / (π * t)) * Real.sin t := by
  have h := Phi_bessel (l := 1 / 2) (by norm_num) ht
  rw [Phi_half_ofReal ht.ne'] at h
  have h' := Complex.ofReal_injective h
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq, ← Real.sqrt_eq_rpow] at h'
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hq : Real.sqrt (2 / t) * Real.sqrt (2 / (π * t)) = 2 / (Real.sqrt π * t) := by
    refine sqrt_mul_sqrt_eq (by positivity) (by positivity) ?_
    rw [div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hcpos : 0 < 1 / 2 * Real.sqrt π * Real.sqrt (2 / t) := by
    have : 0 < Real.sqrt (2 / t) := Real.sqrt_pos.mpr (by positivity)
    positivity
  apply mul_left_cancel₀ hcpos.ne'
  rw [← h']
  calc Real.sin t / t
      = (Real.sqrt π / Real.sqrt π) * (Real.sin t / t) := by rw [div_self hs.ne', one_mul]
    _ = 1 / 2 * Real.sqrt π * (2 / (Real.sqrt π * t)) * Real.sin t := by ring
    _ = _ := by rw [← hq]; ring

/-- The closed form `J_{-1/2}(t) = √(2/(πt)) cos t`, proved from the series and the cosine series. -/
theorem besselJ_neg_half {t : ℝ} (ht : 0 < t) :
    besselJ (-1 / 2) t = Real.sqrt (2 / (π * t)) * Real.cos t := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have key : ∀ n : ℕ, (-1 : ℝ) ^ n / ((n.factorial : ℝ) * Real.Gamma (n + -1 / 2 + 1)) *
      ((t / 2) ^ 2) ^ n = (Real.sqrt π)⁻¹ * ((-1) ^ n * t ^ (2 * n) / ((2 * n).factorial : ℝ)) := by
    intro n
    rw [show (n : ℝ) + -1 / 2 + 1 = n + 1 / 2 by ring, Gamma_nat_add_half, ← pochhammer_half n,
      div_pow t 2 2, show (2 : ℝ) ^ 2 = 4 by norm_num, div_pow, pow_mul]
    ring
  have hsum : HasSum (fun n : ℕ => (Real.sqrt π)⁻¹ * ((-1) ^ n * t ^ (2 * n) /
      ((2 * n).factorial : ℝ))) ((Real.sqrt π)⁻¹ * Real.cos t) :=
    (Real.hasSum_cos t).mul_left _
  have e2 : Real.sqrt (2 / (π * t)) = Real.sqrt (2 / t) / Real.sqrt π := by
    rw [show 2 / (π * t) = 2 / t / π by ring]
    exact Real.sqrt_div (by positivity) π
  rw [besselJ, tsum_congr key, hsum.tsum_eq, rpow_neg_half (by positivity), inv_div, e2]
  ring

/-! ## Corollary 4.2 -/

/-- `Im G^out_{3,k}(ρ) = sin(kρ)/(4πρ)`, the imaginary part of `e^{ikρ}/(4πρ)`; this uses only the
proved closed form of `J_{1/2}`. -/
theorem Gout_three_im (Y : ℝ → ℝ → ℝ) {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    (Gout Y 3 k ρ).im = Real.sin (k * ρ) / (4 * π * ρ) := by
  rw [Gout_im, show (((3 : ℕ) : ℝ) - 2) / 2 = 1 / 2 by norm_num, besselJ_half (mul_pos hk hρ),
    ← Real.sqrt_eq_rpow]
  have hp : Real.sqrt (k / (2 * π * ρ)) * Real.sqrt (2 / (π * (k * ρ))) = 1 / (π * ρ) := by
    refine sqrt_mul_sqrt_eq (by positivity) (by positivity) ?_
    rw [div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [← mul_assoc, hp]
  ring

/-- The full kernel `G^out_{3,k}(ρ) = e^{ikρ}/(4πρ)`, from the classical closed form of `Y_{1/2}`
(explicit hypothesis `hY`). -/
theorem Gout_three (Y : ℝ → ℝ → ℝ)
    (hY : ∀ t : ℝ, 0 < t → Y (1 / 2) t = -(Real.sqrt (2 / (π * t)) * Real.cos t))
    {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    Gout Y 3 k ρ = cexp (I * k * ρ) / (4 * π * ρ) := by
  have hkρ := mul_pos hk hρ
  unfold Gout hankel1
  rw [show (((3 : ℕ) : ℝ) - 2) / 2 = 1 / 2 by norm_num, besselJ_half hkρ, hY _ hkρ,
    ← Real.sqrt_eq_rpow]
  have hp : Real.sqrt (k / (2 * π * ρ)) * Real.sqrt (2 / (π * (k * ρ))) * π * ρ = 1 := by
    rw [sqrt_mul_sqrt_eq (by positivity) (by positivity)
      (show k / (2 * π * ρ) * (2 / (π * (k * ρ))) = (1 / (π * ρ)) ^ 2 by
        rw [div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]; ring),
      mul_assoc, one_div, inv_mul_cancel₀ (by positivity)]
  have hpc : ((Real.sqrt (k / (2 * π * ρ)) : ℝ) : ℂ) * ((Real.sqrt (2 / (π * (k * ρ))) : ℝ) : ℂ) *
      (π : ℂ) * (ρ : ℂ) = 1 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hp
    simp only [Complex.ofReal_mul, Complex.ofReal_one] at this
    exact this
  have hne : (4 * (π : ℂ) * (ρ : ℂ)) ≠ 0 := by
    have : (4 * π * ρ : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  rw [show I * (k : ℂ) * (ρ : ℂ) = ((k * ρ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, eq_div_iff hne, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_mul]
  linear_combination (I * ((Real.sin (k * ρ) : ℝ) : ℂ) + ((Real.cos (k * ρ) : ℝ) : ℂ)) * hpc -
    (((Real.sqrt (k / (2 * π * ρ)) : ℝ) : ℂ) * ((Real.sqrt (2 / (π * (k * ρ))) : ℝ) : ℂ) *
      (π : ℂ) * (ρ : ℂ) * ((Real.cos (k * ρ) : ℝ) : ℂ)) * I_sq

/-! ## Proposition 4.3: the endpoints `d = 1, 2` -/

/-- The symmetric two-point measure `ν_{-1/2} = (δ_{-1} + δ_1)/2`. -/
def nuEndpoint : Measure ℝ := ENNReal.ofReal (1 / 2) • (Measure.dirac (-1) + Measure.dirac 1)

/-- Its characteristic function `Φ_{-1/2}(z) = ∫ e^{izu} dν_{-1/2}(u)`. -/
def PhiEndpoint (z : ℂ) : ℂ := ∫ u, cexp (I * z * u) ∂nuEndpoint

theorem integral_nuEndpoint (f : ℝ → ℂ) : ∫ u, f u ∂nuEndpoint = (f (-1) + f 1) / 2 := by
  have h1 : Integrable f (Measure.dirac (-1 : ℝ)) := by
    first
      | exact integrable_dirac enorm_lt_top
      | exact integrable_dirac (by simp)
  have h2 : Integrable f (Measure.dirac (1 : ℝ)) := by
    first
      | exact integrable_dirac enorm_lt_top
      | exact integrable_dirac (by simp)
  rw [nuEndpoint, integral_smul_measure, integral_add_measure h1 h2, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by norm_num), Complex.real_smul]
  push_cast
  ring

theorem nuEndpoint_isProbability : IsProbabilityMeasure nuEndpoint := by
  constructor
  rw [nuEndpoint, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one zero_le_one, ← ENNReal.ofReal_mul
      (by norm_num)]
  norm_num

/-- The even moments of `ν_{-1/2}` are `1`. -/
theorem nuEndpoint_moment_even (n : ℕ) : ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂nuEndpoint = 1 := by
  rw [integral_nuEndpoint, (even_two_mul n).neg_one_pow, one_pow]
  push_cast
  ring

/-- The odd moments of `ν_{-1/2}` vanish. -/
theorem nuEndpoint_moment_odd (n : ℕ) : ∫ u, ((u ^ (2 * n + 1) : ℝ) : ℂ) ∂nuEndpoint = 0 := by
  rw [integral_nuEndpoint, (odd_two_mul_add_one n).neg_one_pow, one_pow]
  push_cast
  ring

/-- The weak-limit remark: the even moments `(1/2)_n/(λ+1)_n` of `ν_λ` tend, as `λ ↓ -1/2`, to
those of the two-point measure `ν_{-1/2}` (the odd moments vanish on both sides). -/
theorem nuEndpoint_moment_limit (n : ℕ) :
    Tendsto (fun l : ℝ => ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(ν l)) (𝓝[>] (-1 / 2))
      (𝓝 (∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂nuEndpoint)) := by
  have hP : (ascPochhammer ℝ n).eval (1 / 2 : ℝ) ≠ 0 := (ascPochhammer_pos n _ (by norm_num)).ne'
  have hc : Tendsto (fun l : ℝ => (ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (l + 1))
      (𝓝 (-1 / 2)) (𝓝 ((ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (-1 / 2 + 1))) := by
    apply Tendsto.div tendsto_const_nhds
    · exact ((Polynomial.continuous (p := ascPochhammer ℝ n)).comp
        (continuous_id.add continuous_const)).continuousAt
    · rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num]; exact hP
  rw [show (-1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, div_self hP] at hc
  have hc' := ((Complex.continuous_ofReal.tendsto 1).comp hc).mono_left
    (nhdsWithin_le_nhds (s := Ioi (-1 / 2 : ℝ)))
  rw [Complex.ofReal_one] at hc'
  rw [nuEndpoint_moment_even]
  refine hc'.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with l hl
  rw [Function.comp_apply, GegenbauerFock.Manuscript13.moment_even hl]

/-- `Φ_{-1/2}(z) = cos z`. -/
theorem PhiEndpoint_eq_cos (z : ℂ) : PhiEndpoint z = Complex.cos z := by
  rw [PhiEndpoint, integral_nuEndpoint,
    show I * z * ((-1 : ℝ) : ℂ) = -z * I by push_cast; ring,
    show I * z * ((1 : ℝ) : ℂ) = z * I by push_cast; ring]
  linear_combination (-1 / 2 : ℂ) * Complex.two_cos (x := z)

/-- `Im G^out_{1,k}(ρ) = cos(kρ)/(2k)`, from the proved closed form of `J_{-1/2}`. -/
theorem Gout_one_im (Y : ℝ → ℝ → ℝ) {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    (Gout Y 1 k ρ).im = Real.cos (k * ρ) / (2 * k) := by
  rw [Gout_im, show (((1 : ℕ) : ℝ) - 2) / 2 = -1 / 2 by norm_num, besselJ_neg_half (mul_pos hk hρ),
    rpow_neg_half (by positivity)]
  have hp : Real.sqrt (k / (2 * π * ρ))⁻¹ * Real.sqrt (2 / (π * (k * ρ))) = 2 / k := by
    refine sqrt_mul_sqrt_eq (by positivity) (by positivity) ?_
    rw [inv_div, div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    ring
  rw [← mul_assoc, hp]
  ring

/-- The full kernel `G^out_{1,k}(ρ) = (i/2) e^{ikρ}/k`, `eq:one-d-outgoing-proof`, from the classical closed form
of `Y_{-1/2}` (explicit hypothesis `hY`). -/
theorem Gout_one (Y : ℝ → ℝ → ℝ)
    (hY : ∀ t : ℝ, 0 < t → Y (-1 / 2) t = Real.sqrt (2 / (π * t)) * Real.sin t)
    {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    Gout Y 1 k ρ = I / 2 * cexp (I * k * ρ) / k := by
  have hkρ := mul_pos hk hρ
  unfold Gout hankel1
  rw [show (((1 : ℕ) : ℝ) - 2) / 2 = -1 / 2 by norm_num, besselJ_neg_half hkρ, hY _ hkρ,
    rpow_neg_half (by positivity)]
  have hp : Real.sqrt (k / (2 * π * ρ))⁻¹ * Real.sqrt (2 / (π * (k * ρ))) * k = 2 := by
    rw [sqrt_mul_sqrt_eq (by positivity) (by positivity)
      (show (k / (2 * π * ρ))⁻¹ * (2 / (π * (k * ρ))) = (2 / k) ^ 2 by
        rw [inv_div, div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
        ring),
      div_mul_cancel₀ _ hk.ne']
  have hpc : ((Real.sqrt (k / (2 * π * ρ))⁻¹ : ℝ) : ℂ) * ((Real.sqrt (2 / (π * (k * ρ))) : ℝ) : ℂ) *
      (k : ℂ) = 2 := by
    have := congrArg (fun r : ℝ => (r : ℂ)) hp
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at this
    exact this
  have hne : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  rw [show I * (k : ℂ) * (ρ : ℂ) = ((k * ρ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, eq_div_iff hne, Complex.ofReal_mul,
    Complex.ofReal_mul]
  linear_combination (I / 4 * (((Real.cos (k * ρ) : ℝ) : ℂ) + I * ((Real.sin (k * ρ) : ℝ) : ℂ))) * hpc

/-- `Im G^out_{2,k}(ρ) = J_0(kρ)/4`. -/
theorem Gout_two_im (Y : ℝ → ℝ → ℝ) (k ρ : ℝ) :
    (Gout Y 2 k ρ).im = besselJ 0 (k * ρ) / 4 := by
  rw [Gout_im, show (((2 : ℕ) : ℝ) - 2) / 2 = 0 by norm_num, Real.rpow_zero, one_mul]

/-- `Φ_0(t) = J_0(t)` for `t > 0` (arcsine measure `ν_0`). -/
theorem Phi_zero_bessel {t : ℝ} (ht : 0 < t) : Φ 0 (t : ℂ) = ((besselJ 0 t : ℝ) : ℂ) := by
  rw [Phi_bessel (l := 0) (by norm_num) ht, zero_add, Real.Gamma_one, Real.rpow_zero, one_mul,
    one_mul]

/-- **Proposition 4.3**, `eq:resolvent-low-d`, `eq:resolvent-low-d-two`, for `k, ρ > 0`. -/
theorem proposition_4_3 (Y : ℝ → ℝ → ℝ) {k ρ : ℝ} (hk : 0 < k) (hρ : 0 < ρ) :
    PhiEndpoint ((k * ρ : ℝ) : ℂ) = ((Real.cos (k * ρ) : ℝ) : ℂ) ∧
      Real.cos (k * ρ) = 2 * k * (Gout Y 1 k ρ).im ∧
      Φ 0 ((k * ρ : ℝ) : ℂ) = ((besselJ 0 (k * ρ) : ℝ) : ℂ) ∧
      besselJ 0 (k * ρ) = 4 * (Gout Y 2 k ρ).im := by
  refine ⟨?_, ?_, Phi_zero_bessel (mul_pos hk hρ), ?_⟩
  · rw [PhiEndpoint_eq_cos, Complex.ofReal_cos]
  · rw [Gout_one_im Y hk hρ, mul_div_assoc', eq_div_iff (by positivity)]
    ring
  · rw [Gout_two_im]
    ring

/-- **Proposition 4.3**, the continuous values at `ρ = 0`. -/
theorem proposition_4_3_origin (Y : ℝ → ℝ → ℝ) {k : ℝ} (hk : 0 < k) :
    PhiEndpoint 0 = 1 ∧ Φ 0 0 = 1 ∧
      Tendsto (fun ρ : ℝ => 2 * k * (Gout Y 1 k ρ).im) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun ρ : ℝ => 4 * (Gout Y 2 k ρ).im) (𝓝[>] 0) (𝓝 1) := by
  refine ⟨by rw [PhiEndpoint_eq_cos, Complex.cos_zero], Phi_zero (by norm_num), ?_, ?_⟩
  · have hc : Continuous fun ρ : ℝ => Real.cos (k * ρ) :=
      Real.continuous_cos.comp (continuous_const.mul continuous_id)
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [mul_zero, Real.cos_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
    exact (proposition_4_3 Y hk hρ).2.1
  · have hc : Continuous fun ρ : ℝ => (Φ 0 ((k * ρ : ℝ) : ℂ)).re :=
      Complex.continuous_re.comp ((continuous_Phi_ofReal (by norm_num)).comp
        (continuous_const.mul continuous_id))
    have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [mul_zero, Complex.ofReal_zero, Phi_zero (by norm_num), Complex.one_re] at h
    refine h.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with ρ hρ
    rw [Phi_zero_bessel (mul_pos hk hρ), Complex.ofReal_re, Gout_two_im]
    ring

/-! ## Table 1 -/

theorem A_odd {k : ℝ} (hk : 0 < k) (m : ℕ) :
    A (2 * m + 3) k = 8 * π * (ascPochhammer ℝ (m + 1)).eval (1 / 2) * (4 * π / k ^ 2) ^ m / k := by
  unfold A
  have hx : 0 ≤ 4 * π / k ^ 2 := by positivity
  rw [show (((2 * m + 3 : ℕ) : ℝ) / 2) = ((m + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring,
    Gamma_nat_add_half, show 2 * m + 3 - 2 = 2 * m + 1 by omega,
    show (4 * π / k ^ 2) ^ (2 * m + 1) = ((4 * π / k ^ 2) ^ m) ^ 2 * (4 * π / k ^ 2) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), sqrt_four_pi_div hk,
    show 8 * π = 8 * (Real.sqrt π * Real.sqrt π) by rw [Real.mul_self_sqrt Real.pi_pos.le]]
  ring

theorem A_even {k : ℝ} (m : ℕ) :
    A (2 * m + 4) k = 4 * ((m + 1).factorial : ℝ) * (4 * π / k ^ 2) ^ (m + 1) := by
  unfold A
  rw [show (((2 * m + 4 : ℕ) : ℝ) / 2) = ((m + 1 : ℕ) : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, show 2 * m + 4 - 2 = 2 * (m + 1) by omega, pow_mul',
    Real.sqrt_sq (by positivity)]

theorem poch_half_1 : (ascPochhammer ℝ 1).eval (1 / 2 : ℝ) = 1 / 2 := by
  rw [ascPochhammer_one, Polynomial.eval_X]
theorem poch_half_2 : (ascPochhammer ℝ 2).eval (1 / 2 : ℝ) = 3 / 4 := by
  have h := ascPochhammer_succ_eval (S := ℝ) 1 (1 / 2)
  rw [poch_half_1] at h
  exact h.trans (by norm_num)
theorem poch_half_3 : (ascPochhammer ℝ 3).eval (1 / 2 : ℝ) = 15 / 8 := by
  have h := ascPochhammer_succ_eval (S := ℝ) 2 (1 / 2)
  rw [poch_half_2] at h
  exact h.trans (by norm_num)
theorem poch_half_4 : (ascPochhammer ℝ 4).eval (1 / 2 : ℝ) = 105 / 16 := by
  have h := ascPochhammer_succ_eval (S := ℝ) 3 (1 / 2)
  rw [poch_half_3] at h
  exact h.trans (by norm_num)
theorem poch_half_5 : (ascPochhammer ℝ 5).eval (1 / 2 : ℝ) = 945 / 32 := by
  have h := ascPochhammer_succ_eval (S := ℝ) 4 (1 / 2)
  rw [poch_half_4] at h
  exact h.trans (by norm_num)

/-- **Table 1**, `d = 3, …, 12`: the exact coefficients `A_d(k)`. -/
theorem table_1 {k : ℝ} (hk : 0 < k) :
    A 3 k = 4 * π / k ∧ A 4 k = 16 * π / k ^ 2 ∧ A 5 k = 24 * π ^ 2 / k ^ 3 ∧
      A 6 k = 128 * π ^ 2 / k ^ 4 ∧ A 7 k = 240 * π ^ 3 / k ^ 5 ∧
      A 8 k = 1536 * π ^ 3 / k ^ 6 ∧ A 9 k = 3360 * π ^ 4 / k ^ 7 ∧
      A 10 k = 24576 * π ^ 4 / k ^ 8 ∧ A 11 k = 60480 * π ^ 5 / k ^ 9 ∧
      A 12 k = 491520 * π ^ 5 / k ^ 10 := by
  have o0 : A 3 k = 8 * π * (ascPochhammer ℝ 1).eval (1 / 2) * (4 * π / k ^ 2) ^ 0 / k :=
    A_odd hk 0
  have o1 : A 5 k = 8 * π * (ascPochhammer ℝ 2).eval (1 / 2) * (4 * π / k ^ 2) ^ 1 / k :=
    A_odd hk 1
  have o2 : A 7 k = 8 * π * (ascPochhammer ℝ 3).eval (1 / 2) * (4 * π / k ^ 2) ^ 2 / k :=
    A_odd hk 2
  have o3 : A 9 k = 8 * π * (ascPochhammer ℝ 4).eval (1 / 2) * (4 * π / k ^ 2) ^ 3 / k :=
    A_odd hk 3
  have o4 : A 11 k = 8 * π * (ascPochhammer ℝ 5).eval (1 / 2) * (4 * π / k ^ 2) ^ 4 / k :=
    A_odd hk 4
  have e0 : A 4 k = 4 * ((1 : ℕ).factorial : ℝ) * (4 * π / k ^ 2) ^ 1 := A_even 0
  have e1 : A 6 k = 4 * ((2 : ℕ).factorial : ℝ) * (4 * π / k ^ 2) ^ 2 := A_even 1
  have e2 : A 8 k = 4 * ((3 : ℕ).factorial : ℝ) * (4 * π / k ^ 2) ^ 3 := A_even 2
  have e3 : A 10 k = 4 * ((4 : ℕ).factorial : ℝ) * (4 * π / k ^ 2) ^ 4 := A_even 3
  have e4 : A 12 k = 4 * ((5 : ℕ).factorial : ℝ) * (4 * π / k ^ 2) ^ 5 := A_even 4
  rw [poch_half_1] at o0
  rw [poch_half_2] at o1
  rw [poch_half_3] at o2
  rw [poch_half_4] at o3
  rw [poch_half_5] at o4
  rw [show (1 : ℕ).factorial = 1 from rfl] at e0
  rw [show (2 : ℕ).factorial = 2 from rfl] at e1
  rw [show (3 : ℕ).factorial = 6 from rfl] at e2
  rw [show (4 : ℕ).factorial = 24 from rfl] at e3
  rw [show (5 : ℕ).factorial = 120 from rfl] at e4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [o0]; ring
  · rw [e0]; push_cast; ring
  · rw [o1]; ring
  · rw [e1]; push_cast; ring
  · rw [o2]; ring
  · rw [e2]; push_cast; ring
  · rw [o3]; ring
  · rw [e3]; push_cast; ring
  · rw [o4]; ring
  · rw [e4]; push_cast; ring

/-- **Table 1**, endpoint rows: the real-power coefficient `eq:dimensional-factor-proof` gives `2k` at `d = 1` and `4` at
`d = 2`, the constants of Proposition 4.3. -/
theorem table_1_endpoints {k : ℝ} (hk : 0 < k) : Arpow 1 k = 2 * k ∧ Arpow 2 k = 4 := by
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  constructor
  · unfold Arpow
    rw [show ((1 : ℕ) : ℝ) / 2 = 1 / 2 by norm_num, show (((1 : ℕ) : ℝ) - 2) / 2 = -(1 / 2) by norm_num,
      Real.Gamma_one_half_eq, Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow,
      sqrt_four_pi_div hk, inv_div]
    calc 4 * Real.sqrt π * (k / (2 * Real.sqrt π))
        = 2 * k * (Real.sqrt π / Real.sqrt π) := by ring
      _ = 2 * k := by rw [div_self hs.ne', mul_one]
  · unfold Arpow
    rw [show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num, show (((2 : ℕ) : ℝ) - 2) / 2 = 0 by norm_num,
      Real.Gamma_one, Real.rpow_zero]
    ring

/-! ## Corollary 4.2 -/

theorem A_three_half : A 3 (1 / 2) = 8 * π := by
  rw [(table_1 (k := 1 / 2) (by norm_num)).1]
  ring

/-- **Corollary 4.2**, `eq:eulerian-resolvent`, for `ρ > 0`. -/
theorem corollary_4_2 (Y : ℝ → ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    rE (ρ : ℂ) = ((8 * π * (Gout Y 3 (1 / 2) ρ).im : ℝ) : ℂ) ∧
      8 * π * (Gout Y 3 (1 / 2) ρ).im = Real.sin (ρ / 2) / (ρ / 2) := by
  have h2 : 8 * π * (Gout Y 3 (1 / 2) ρ).im = Real.sin (ρ / 2) / (ρ / 2) := by
    rw [Gout_three_im Y (by norm_num) hρ, show 1 / 2 * ρ = ρ / 2 by ring, mul_div_assoc',
      div_eq_div_iff (by positivity) (by positivity)]
    ring
  exact ⟨by rw [h2, rE_ofReal hρ.ne'], h2⟩

/-- **Corollary 4.2** at the origin: `r_E(0) = 1` and `8π Im G^out_{3,1/2}(ρ) → 1` as `ρ ↓ 0`;
the factor of Theorem 4.1 at `d = 3`, `k = 1/2` is `8π`. -/
theorem corollary_4_2_origin (Y : ℝ → ℝ → ℝ) :
    rE 0 = 1 ∧ A 3 (1 / 2) = 8 * π ∧
      Tendsto (fun ρ : ℝ => 8 * π * (Gout Y 3 (1 / 2) ρ).im) (𝓝[>] 0) (𝓝 1) := by
  refine ⟨?_, A_three_half, ?_⟩
  · rw [rE_eq_Phi, zero_div, Phi_zero (by norm_num)]
  · have h := theorem_4_1_extension Y (d := 3) (by norm_num) (k := 1 / 2) (by norm_num)
    change Tendsto (fun ρ : ℝ => A 3 (1 / 2) * (Gout Y 3 (1 / 2) ρ).im) (𝓝[>] 0) (𝓝 1) at h
    rw [A_three_half] at h
    exact h

/-! ## Proposition 4.4: sphere averages and positive definiteness -/

/-- The plane wave `ω ↦ e^{ik ω·x}` on the unit sphere `S^{d-1}`. -/
def planeWave (d : ℕ) (k : ℝ) (x : EuclideanSpace ℝ (Fin d))
    (ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) : ℂ :=
  cexp (I * (k : ℂ) * ((inner ℝ (ω : EuclideanSpace ℝ (Fin d)) x : ℝ) : ℂ))

/-- **Classical input** (rotation invariance and the marginal law `eq:nu` of the uniform measure
`σ_{d-1}`): for every unit vector `e`, the law of `ω ↦ ω·e` under `σ` is `ν_{(d-2)/2}`. -/
def ZonalMarginal (d : ℕ) (σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) : Prop :=
  ∀ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 →
    σ.map (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => inner ℝ (ω : EuclideanSpace ℝ (Fin d)) e) = ν (((d : ℝ) - 2) / 2)

theorem exists_unit_smul {d : ℕ} (hd : 1 ≤ d) (x : EuclideanSpace ℝ (Fin d)) :
    ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧ x = ‖x‖ • e := by
  by_cases hx : x = 0
  · refine ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, ?_, ?_⟩
    · rw [EuclideanSpace.norm_single, norm_one]
    · rw [hx, norm_zero, zero_smul]
  · refine ⟨‖x‖⁻¹ • x, norm_smul_inv_norm hx, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem measurable_inner_sphere {d : ℕ} (e : EuclideanSpace ℝ (Fin d)) :
    Measurable fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 =>
      inner ℝ (ω : EuclideanSpace ℝ (Fin d)) e :=
  (continuous_subtype_val.inner continuous_const).measurable

/-- A measure with the zonal marginal property is a probability measure. -/
theorem isProbability_of_zonal {d : ℕ} (hd : 3 ≤ d)
    {σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)} (hσ : ZonalMarginal d σ) :
    IsProbabilityMeasure σ := by
  obtain ⟨e, he, -⟩ := exists_unit_smul (by omega) (0 : EuclideanSpace ℝ (Fin d))
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  haveI := isProbability (l := ((d : ℝ) - 2) / 2) (by linarith)
  constructor
  have h := Measure.map_apply (μ := σ) (measurable_inner_sphere e) MeasurableSet.univ
  rw [hσ e he, Set.preimage_univ] at h
  rw [← h]
  exact measure_univ

/-- `eq:sphere-average`: `∫_{S^{d-1}} e^{ik ω·x} dσ(ω) = Φ_{(d-2)/2}(k|x|)`. -/
theorem sphere_average {d : ℕ} (hd : 3 ≤ d)
    {σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)} (hσ : ZonalMarginal d σ)
    (k : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ ω, planeWave d k x ω ∂σ = Φ (((d : ℝ) - 2) / 2) ((k * ‖x‖ : ℝ) : ℂ) := by
  obtain ⟨e, he, hx⟩ := exists_unit_smul (by omega) x
  have hpw : ∀ ω, planeWave d k x ω = cexp (I * ((k * ‖x‖ : ℝ) : ℂ) *
      ((inner ℝ (ω : EuclideanSpace ℝ (Fin d)) e : ℝ) : ℂ)) := by
    intro ω
    unfold planeWave
    conv_lhs => rw [hx]
    rw [real_inner_smul_right]
    congr 1
    push_cast
    ring
  have hmap := integral_map (μ := σ) (measurable_inner_sphere e).aemeasurable
    (f := fun u : ℝ => cexp (I * ((k * ‖x‖ : ℝ) : ℂ) * (u : ℂ)))
    ((by fun_prop : Continuous fun u : ℝ => cexp (I * ((k * ‖x‖ : ℝ) : ℂ) * (u : ℂ))).aestronglyMeasurable)
  calc ∫ ω, planeWave d k x ω ∂σ
      = ∫ ω, cexp (I * ((k * ‖x‖ : ℝ) : ℂ) * ((inner ℝ (ω : EuclideanSpace ℝ (Fin d)) e : ℝ) : ℂ)) ∂σ :=
        integral_congr_ae (ae_of_all _ hpw)
    _ = ∫ u, cexp (I * ((k * ‖x‖ : ℝ) : ℂ) * (u : ℂ))
          ∂(σ.map fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 => inner ℝ (ω : EuclideanSpace ℝ (Fin d)) e) := hmap.symm
    _ = Φ (((d : ℝ) - 2) / 2) ((k * ‖x‖ : ℝ) : ℂ) := by rw [hσ e he]; rfl

/-- The kernel of Proposition 4.4, `eq:resolvent-positive-kernel`: `K_{d,k}(x,y) = Φ_{(d-2)/2}(k|x-y|)`. -/
def K (d : ℕ) (k : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Φ (((d : ℝ) - 2) / 2) ((k * ‖x - y‖ : ℝ) : ℂ)

theorem K_eq_integral {d : ℕ} (hd : 3 ≤ d)
    {σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)} (hσ : ZonalMarginal d σ)
    (k : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    K d k x y = ∫ ω, planeWave d k x ω * conj (planeWave d k y ω) ∂σ := by
  rw [K, ← sphere_average hd hσ k (x - y)]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  dsimp only
  unfold planeWave
  rw [← Complex.exp_conj, ← Complex.exp_add, inner_sub_right]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The quadratic form of `eq:resolvent-positive-proof`: `∑ a_j ā_l K(x_j,x_l) = ∫ |∑ a_j e^{ik ω·x_j}|² dσ`. -/
theorem quadratic_form_eq {d : ℕ} (hd : 3 ≤ d)
    {σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)} (hσ : ZonalMarginal d σ)
    (k : ℝ) {N : ℕ} (xs : Fin N → EuclideanSpace ℝ (Fin d)) (a : Fin N → ℂ) :
    ∑ j, ∑ l, a j * conj (a l) * K d k (xs j) (xs l) =
      ((∫ ω, Complex.normSq (∑ j, a j * planeWave d k (xs j) ω) ∂σ : ℝ) : ℂ) := by
  haveI := isProbability_of_zonal hd hσ
  have hpwc : ∀ x, Continuous (planeWave d k x) := fun x => by unfold planeWave; fun_prop
  have hpwn : ∀ x ω, ‖planeWave d k x ω‖ = 1 := fun x ω => norm_cexp_I_mul _ _
  have hint : ∀ j l, Integrable (fun ω => a j * conj (a l) *
      (planeWave d k (xs j) ω * conj (planeWave d k (xs l) ω))) σ := by
    intro j l
    refine (integrable_const (‖a j‖ * ‖a l‖)).mono'
      (continuous_const.mul ((hpwc _).mul (Complex.continuous_conj.comp (hpwc _)))).aestronglyMeasurable
      (ae_of_all _ fun ω => le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj, hpwn, hpwn, mul_one,
      mul_one]
  calc ∑ j, ∑ l, a j * conj (a l) * K d k (xs j) (xs l)
      = ∑ j, ∑ l, ∫ ω, a j * conj (a l) *
          (planeWave d k (xs j) ω * conj (planeWave d k (xs l) ω)) ∂σ := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [K_eq_integral hd hσ, integral_const_mul]
    _ = ∫ ω, ∑ j, ∑ l, a j * conj (a l) *
          (planeWave d k (xs j) ω * conj (planeWave d k (xs l) ω)) ∂σ := by
        rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun l _ => hint j l))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finset_sum _ (fun l _ => hint j l)]
    _ = ∫ ω, ((Complex.normSq (∑ j, a j * planeWave d k (xs j) ω) : ℝ) : ℂ) ∂σ := by
        refine integral_congr_ae (ae_of_all _ fun ω => ?_)
        dsimp only
        rw [← mul_conj_eq, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        rw [map_mul]
        ring
    _ = _ := integral_complex_ofReal

/-- **Proposition 4.4**: `K_{d,k}` equals `A_d(k) Im G^out_{d,k}(|x-y|)` off the diagonal, is
real-valued and continuous, satisfies `K(x,x) = 1`, and is positive definite. -/
theorem proposition_4_4 (Y : ℝ → ℝ → ℝ) {d : ℕ} (hd : 3 ≤ d) {k : ℝ} (hk : 0 < k)
    {σ : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)} (hσ : ZonalMarginal d σ) :
    (∀ x y : EuclideanSpace ℝ (Fin d), x ≠ y →
        K d k x y = ((A d k * (Gout Y d k ‖x - y‖).im : ℝ) : ℂ)) ∧
      (∀ x y : EuclideanSpace ℝ (Fin d), (K d k x y).im = 0) ∧
      (∀ x : EuclideanSpace ℝ (Fin d), K d k x x = 1) ∧
      Continuous (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) => K d k p.1 p.2) ∧
      (∀ (N : ℕ) (xs : Fin N → EuclideanSpace ℝ (Fin d)) (a : Fin N → ℂ),
        (∑ j, ∑ l, a j * conj (a l) * K d k (xs j) (xs l)).im = 0 ∧
          0 ≤ (∑ j, ∑ l, a j * conj (a l) * K d k (xs j) (xs l)).re) := by
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hl : (-1 / 2 : ℝ) < ((d : ℝ) - 2) / 2 := by linarith
  refine ⟨fun x y hxy => ?_, fun x y => ?_, fun x => ?_, ?_, fun N xs a => ?_⟩
  · rw [K, theorem_4_1 Y hd hk (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))]
    rfl
  · exact Phi_ofReal_im hl (mul_nonneg hk.le (norm_nonneg _))
  · rw [K, sub_self, norm_zero, mul_zero, Complex.ofReal_zero, Phi_zero hl]
  · exact (continuous_Phi_ofReal hl).comp (by fun_prop)
  · rw [quadratic_form_eq hd hσ k xs a, Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨rfl, integral_nonneg fun ω => Complex.normSq_nonneg _⟩

#print axioms GegenbauerFock.Section4Resolvent.theorem_4_1
#print axioms GegenbauerFock.Section4Resolvent.theorem_4_1_extension
#print axioms GegenbauerFock.Section4Resolvent.theorem_4_1_diagonal
#print axioms GegenbauerFock.Section4Resolvent.corollary_4_2
#print axioms GegenbauerFock.Section4Resolvent.corollary_4_2_origin
#print axioms GegenbauerFock.Section4Resolvent.besselJ_half
#print axioms GegenbauerFock.Section4Resolvent.besselJ_neg_half
#print axioms GegenbauerFock.Section4Resolvent.Gout_three
#print axioms GegenbauerFock.Section4Resolvent.Gout_one
#print axioms GegenbauerFock.Section4Resolvent.proposition_4_3
#print axioms GegenbauerFock.Section4Resolvent.proposition_4_3_origin
#print axioms GegenbauerFock.Section4Resolvent.nuEndpoint_moment_limit
#print axioms GegenbauerFock.Section4Resolvent.sphere_average
#print axioms GegenbauerFock.Section4Resolvent.proposition_4_4
#print axioms GegenbauerFock.Section4Resolvent.table_1
#print axioms GegenbauerFock.Section4Resolvent.table_1_endpoints

end GegenbauerFock.Section4Resolvent
