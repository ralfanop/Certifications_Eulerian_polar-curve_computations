import GegenbauerFock.Manuscript13Measure
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Polynomial

/-! # Manuscript 13, Propositions 3.3, 3.4 and 3.6

`Φ_λ(z) = ∫ e^{izu} dν_λ(u)`.
* Proposition 3.3: `Φ_λ(z) = Σ_n (-1)^n/(n!(λ+1)_n) (z²/4)^n` for every `z ∈ ℂ`, `Φ_λ(0) = 1`, and
  for `t > 0`, `Φ_λ(t) = Γ(λ+1)(2/t)^λ J_λ(t)` with `J_λ` given by its classical power series.
* Proposition 3.4: `ν_{1/2}` has density `1/2` on `(-1,1)` and `r_E(z) = Φ_{1/2}(z/2)`.
* Proposition 3.6: `ν_1` has density `(2/π)√(1-u²)` and `m_{2n}(1) = C_n/4^n`; the arcsine endpoint
  `ν_0` has density `1/(π√(1-u²))` and `m_{2n}(0) = binom(2n,n)/4^n`; as `λ ↓ 0` the moments and the
  densities converge to those of `ν_0`. -/

open Real MeasureTheory Set intervalIntegral Complex Filter Topology

namespace GegenbauerFock.Manuscript13

noncomputable def Φ (l : ℝ) (z : ℂ) : ℂ := ∫ u, cexp (I * z * u) ∂(ν l)

theorem ae_mem_Icc {l : ℝ} : ∀ᵐ u ∂(ν l), u ∈ Icc (-1:ℝ) 1 := by
  rw [ae_iff]
  change (ν l) (Icc (-1:ℝ) 1)ᶜ = 0
  rw [ν, withDensity_apply _ (measurableSet_Icc.compl)]
  apply setLIntegral_eq_zero (measurableSet_Icc.compl)
  intro u hu
  simp only [dens]
  rw [if_neg (fun h => hu (Ioo_subset_Icc_self h)), ENNReal.ofReal_zero]
  rfl

theorem pochhammer_half (n : ℕ) :
    (ascPochhammer ℝ n).eval (1 / 2) * 4 ^ n * (n.factorial : ℝ) = ((2 * n).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (2 * (n + 1)).factorial = (2 * n + 2) * ((2 * n + 1) * (2 * n).factorial) := by
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ]
    rw [e, ascPochhammer_succ_eval, Nat.factorial_succ]
    push_cast
    rw [← ih]
    ring

theorem pochhammer_pos {l : ℝ} (hl : -1/2 < l) (n : ℕ) : 0 < (ascPochhammer ℝ n).eval (l + 1) :=
  ascPochhammer_pos n (l + 1) (by linarith)

/-- **Proposition 3.3**: the entire power series of `Φ_λ`. -/
theorem Phi_hasSum {l : ℝ} (hl : -1/2 < l) (z : ℂ) :
    HasSum (fun n : ℕ => ((-1:ℂ) ^ n / ((n.factorial : ℂ) * ((ascPochhammer ℝ n).eval (l + 1) : ℝ)))
      * (z ^ 2 / 4) ^ n) (Φ l z) := by
  haveI := isProbability hl
  set F : ℕ → ℝ → ℂ := fun k u => (I * z * u) ^ k / (k.factorial : ℂ) with hF
  have hmeas : ∀ k, AEStronglyMeasurable (F k) (ν l) := fun k =>
    (by fun_prop : Continuous (F k)).aestronglyMeasurable
  have hbound : ∀ k, ∀ᵐ u ∂(ν l), ‖F k u‖ ≤ ‖z‖ ^ k / k.factorial := by
    intro k
    filter_upwards [ae_mem_Icc] with u hu
    have hu1 : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
    simp only [hF, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_natCast]
    gcongr
    calc ‖z‖ * |u| ≤ ‖z‖ * 1 := by gcongr
      _ = ‖z‖ := mul_one _
  have hint : ∀ k, Integrable (F k) (ν l) := fun k =>
    (integrable_const (‖z‖ ^ k / k.factorial : ℝ)).mono' (hmeas k) (hbound k)
  have hsumR : Summable fun k : ℕ => ‖z‖ ^ k / (k.factorial : ℝ) :=
    (NormedSpace.expSeries_div_hasSum_exp ℝ ‖z‖).summable
  have hsum : Summable fun k => ∫ u, ‖F k u‖ ∂(ν l) := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_) hsumR
    calc ∫ u, ‖F k u‖ ∂(ν l) ≤ ∫ u, (‖z‖ ^ k / k.factorial : ℝ) ∂(ν l) :=
          integral_mono_ae (hint k).norm (integrable_const _) (hbound k)
      _ = ‖z‖ ^ k / k.factorial := by simp
  have hexp : ∀ u : ℝ, HasSum (fun k => F k u) (cexp (I * z * u)) := by
    intro u
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp ℂ (I * z * u)
  have hΦ : Φ l z = ∑' k, ∫ u, F k u ∂(ν l) := by
    rw [integral_tsum_of_summable_integral_norm hint hsum, Φ]
    congr 1; funext u; exact (hexp u).tsum_eq.symm
  -- the integrals of the terms
  have hterm : ∀ k, ∫ u, F k u ∂(ν l) = (I * z) ^ k / (k.factorial : ℂ) * ∫ u, ((u ^ k : ℝ) : ℂ) ∂(ν l) := by
    intro k
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext u
    simp only [hF]; push_cast; ring
  have hsumC : Summable fun k => ∫ u, F k u ∂(ν l) :=
    Summable.of_norm_bounded hsum (fun k => norm_integral_le_integral_norm _)
  have hHas : HasSum (fun k => ∫ u, F k u ∂(ν l)) (Φ l z) := by
    rw [hΦ]; exact hsumC.hasSum
  -- odd terms vanish; even terms are the stated ones
  have hodd : ∀ k ∉ Set.range (fun n : ℕ => 2 * n), ∫ u, F k u ∂(ν l) = 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = 2 * n + 1 := by
      rcases Nat.even_or_odd k with ⟨n, hn⟩ | ⟨n, hn⟩
      · exact absurd ⟨n, by simp only; omega⟩ hk
      · exact ⟨n, hn⟩
    rw [hterm, moment_odd hl, mul_zero]
  have hev := ((Function.Injective.hasSum_iff (f := fun k => ∫ u, F k u ∂(ν l))
    (g := fun n : ℕ => 2 * n) (fun a b h => by simpa using h)) hodd).mpr hHas
  convert hev using 1
  funext n
  simp only [Function.comp, hterm, moment_even hl]
  have hf := pochhammer_half n
  have hP := pochhammer_pos hl n
  have hfac : ((2 * n).factorial : ℂ) = (((ascPochhammer ℝ n).eval (1 / 2) : ℝ) : ℂ) * 4 ^ n * (n.factorial : ℂ) := by
    rw [show ((2 * n).factorial : ℂ) = (((2 * n).factorial : ℝ) : ℂ) by norm_cast, ← hf]; push_cast; ring
  rw [hfac, mul_pow, pow_mul, I_sq, div_pow, ← pow_mul]
  have h4 : (4:ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  have hPc : (((ascPochhammer ℝ n).eval (l + 1) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hhalf : (((ascPochhammer ℝ n).eval (1 / 2) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < (ascPochhammer ℝ n).eval (1 / 2 : ℝ) := ascPochhammer_pos n _ (by norm_num)
    exact_mod_cast this.ne'
  push_cast
  field_simp

theorem Phi_zero {l : ℝ} (hl : -1/2 < l) : Φ l 0 = 1 := by
  haveI := isProbability hl
  simp [Φ]

/-- The Bessel function of the first kind, by its classical power series, for `t > 0`. -/
noncomputable def besselJ (l t : ℝ) : ℝ :=
  (t / 2) ^ l * ∑' n : ℕ, (-1) ^ n / ((n.factorial : ℝ) * Real.Gamma (n + l + 1)) * ((t / 2) ^ 2) ^ n

theorem Gamma_pochhammer {l : ℝ} (hl : -1/2 < l) (n : ℕ) :
    Real.Gamma (n + l + 1) = Real.Gamma (l + 1) * (ascPochhammer ℝ n).eval (l + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, show ((n + 1 : ℕ) : ℝ) + l + 1 = (n + l + 1) + 1 by push_cast; ring,
      Real.Gamma_add_one (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith), ih]
    ring

/-- **Proposition 3.3**, Bessel form: `Φ_λ(t) = Γ(λ+1)(2/t)^λ J_λ(t)` for `t > 0`. -/
theorem Phi_bessel {l : ℝ} (hl : -1/2 < l) {t : ℝ} (ht : 0 < t) :
    Φ l t = ((Real.Gamma (l + 1) * (2 / t) ^ l * besselJ l t : ℝ) : ℂ) := by
  have hG : 0 < Real.Gamma (l + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hS := Phi_hasSum hl (t : ℂ)
  set a : ℕ → ℝ := fun n => (-1) ^ n / ((n.factorial : ℝ) * (ascPochhammer ℝ n).eval (l + 1)) *
    (t ^ 2 / 4) ^ n with ha
  have hR : HasSum a (Φ l t).re := by
    have hc : (fun n : ℕ => ((-1:ℂ) ^ n / ((n.factorial : ℂ) * ((ascPochhammer ℝ n).eval (l + 1) : ℝ)))
        * ((t:ℂ) ^ 2 / 4) ^ n) = fun n => ((a n : ℝ) : ℂ) := by
      funext n; simp only [ha]; push_cast; ring
    rw [hc] at hS
    have := Complex.hasSum_re hS
    simpa using this
  have hreal : Φ l t = ((Φ l t).re : ℂ) := by
    have hc : (fun n : ℕ => ((-1:ℂ) ^ n / ((n.factorial : ℂ) * ((ascPochhammer ℝ n).eval (l + 1) : ℝ)))
        * ((t:ℂ) ^ 2 / 4) ^ n) = fun n => ((a n : ℝ) : ℂ) := by
      funext n; simp only [ha]; push_cast; ring
    rw [hc] at hS
    exact hS.unique (Complex.hasSum_ofReal.mpr hR)
  rw [hreal]
  congr 1
  rw [besselJ, ← hR.tsum_eq]
  have hpow : (2 / t) ^ l * (t / 2) ^ l = 1 := by
    rw [← Real.mul_rpow (by positivity) (by positivity), show 2 / t * (t / 2) = 1 by field_simp,
      Real.one_rpow]
  have hterm : ∀ n : ℕ, (-1) ^ n / ((n.factorial : ℝ) * Real.Gamma (n + l + 1)) * ((t / 2) ^ 2) ^ n =
      (Real.Gamma (l + 1))⁻¹ * a n := by
    intro n
    simp only [ha]
    rw [Gamma_pochhammer hl]
    have hP := pochhammer_pos hl n
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left]
  symm
  calc Real.Gamma (l + 1) * (2 / t) ^ l * ((t / 2) ^ l * ((Real.Gamma (l + 1))⁻¹ * ∑' n, a n))
      = ((2 / t) ^ l * (t / 2) ^ l) * (Real.Gamma (l + 1) * (Real.Gamma (l + 1))⁻¹) * ∑' n, a n := by ring
    _ = ∑' n, a n := by rw [hpow, mul_inv_cancel₀ hG.ne']; ring

/-! ## Proposition 3.4 -/

/-- The Eulerian profile, eq. (charfun): `r_E(z) = ∫_{-1/2}^{1/2} e^{izu} du`. -/
noncomputable def rE (z : ℂ) : ℂ := ∫ u in (-1/2:ℝ)..(1/2), cexp (I * z * u)

theorem cl_half : cl (1 / 2) = 1 / 2 := by
  rw [cl, show (1:ℝ) / 2 + 1 = 1 / 2 + 1 by ring, Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq, show (1:ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.Gamma_one]
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

/-- **Proposition 3.4**, (eulerian-uniform-density): `dν_{1/2} = (1/2) 1_{(-1,1)} du`. -/
theorem dens_half (u : ℝ) : dens (1 / 2) u = if u ∈ Ioo (-1:ℝ) 1 then 1 / 2 else 0 := by
  simp only [dens, cl_half]
  split_ifs <;> norm_num

/-- **Proposition 3.4**, (eulerian-ultra): `r_E(z) = Φ_{1/2}(z/2)`. -/
theorem rE_eq_Phi (z : ℂ) : rE z = Φ (1 / 2) (z / 2) := by
  rw [Φ, integral_ν (by norm_num), cl_half]
  simp only [show (1:ℝ) / 2 - 1 / 2 = 0 by norm_num, Real.rpow_zero, mul_one]
  have h := intervalIntegral.integral_comp_div (fun u : ℝ => cexp (I * z * u)) (a := -1) (b := 1)
    (c := 2) (by norm_num)
  rw [rE]
  have e : ∀ u : ℝ, ((1 / 2 : ℝ) : ℂ) * cexp (I * (z / 2) * u) = (1 / 2 : ℂ) * cexp (I * z * ((u / 2 : ℝ) : ℂ)) := by
    intro u; push_cast; ring_nf
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  have h' : ∫ u in (-1:ℝ)..1, cexp (I * z * ((u / 2 : ℝ) : ℂ)) =
      2 * ∫ u in (-1/2:ℝ)..(1/2), cexp (I * z * u) := by
    rw [h]; norm_num
  rw [h']; ring

/-! ## Proposition 3.6 -/

theorem cl_one : cl 1 = 2 / π := by
  rw [cl, show (1:ℝ) + 1 = 2 by norm_num, show (1:ℝ) + 1 / 2 = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq, Real.Gamma_two]
  have hs : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  field_simp
  linarith

theorem cl_zero : cl 0 = 1 / π := by
  rw [cl, zero_add, zero_add, Real.Gamma_one, Real.Gamma_one_half_eq]
  have hsq : Real.sqrt π * Real.sqrt π = π := Real.mul_self_sqrt Real.pi_pos.le
  rw [hsq]

/-- **Proposition 3.6**, (catalan-A-density): `dν_1 = (2/π)√(1-u²) 1_{(-1,1)} du`. -/
theorem dens_one (u : ℝ) : dens 1 u = if u ∈ Ioo (-1:ℝ) 1 then 2 / π * Real.sqrt (1 - u ^ 2) else 0 := by
  simp only [dens, cl_one]
  split_ifs
  · rw [show (1:ℝ) - 1 / 2 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  · rfl

/-- **Proposition 3.6**, (catalan-B-density): the arcsine density `1/(π√(1-u²))`. -/
theorem dens_zero (u : ℝ) : dens 0 u = if u ∈ Ioo (-1:ℝ) 1 then 1 / (π * Real.sqrt (1 - u ^ 2)) else 0 := by
  simp only [dens, cl_zero]
  split_ifs with h
  · have hb : 0 < 1 - u ^ 2 := by nlinarith [h.1, h.2]
    rw [show (0:ℝ) - 1 / 2 = -(1 / 2) by norm_num, Real.rpow_neg hb.le, ← Real.sqrt_eq_rpow]
    field_simp
  · rfl

theorem pochhammer_two (n : ℕ) : (ascPochhammer ℝ n).eval 2 = ((n + 1).factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ (n + 1)]
    push_cast; ring

theorem pochhammer_one (n : ℕ) : (ascPochhammer ℝ n).eval 1 = (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast; ring

/-- **Proposition 3.6**, (catalan-A)–(catalan-numbers): `m_{2n}(1) = C_n/4^n`. -/
theorem moment_one (n : ℕ) :
    ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(ν 1) = (((Nat.choose (2 * n) n : ℝ) / (n + 1)) / 4 ^ n : ℝ) := by
  rw [moment_even (by norm_num), show (1:ℝ) + 1 = 2 by norm_num, pochhammer_two]
  congr 1
  have hf := pochhammer_half n
  rw [Nat.cast_choose ℝ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega, ← hf,
    Nat.factorial_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  push_cast
  field_simp

/-- **Proposition 3.6**, (catalan-B): `m_{2n}(0) = binom(2n,n)/4^n`. -/
theorem moment_zero (n : ℕ) :
    ∫ u, ((u ^ (2 * n) : ℝ) : ℂ) ∂(ν 0) = (((Nat.choose (2 * n) n : ℝ)) / 4 ^ n : ℝ) := by
  rw [moment_even (by norm_num), zero_add, pochhammer_one]
  congr 1
  have hf := pochhammer_half n
  rw [Nat.cast_choose ℝ (by omega : n ≤ 2 * n), show 2 * n - n = n by omega, ← hf]
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  field_simp

/-- **Proposition 3.6**, the limit `λ ↓ 0`: the even moments converge to the arcsine moments. -/
theorem moment_tendsto (n : ℕ) :
    Tendsto (fun l : ℝ => (ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (l + 1))
      (𝓝 0) (𝓝 ((ascPochhammer ℝ n).eval (1 / 2) / (ascPochhammer ℝ n).eval (0 + 1))) := by
  apply Tendsto.div tendsto_const_nhds
  · exact ((Polynomial.continuous (p := ascPochhammer ℝ n)).comp (continuous_id.add continuous_const)).continuousAt
  · exact (ascPochhammer_pos n _ (by norm_num)).ne'

/-- **Proposition 3.6**, the limit `λ ↓ 0`: the densities converge pointwise on `(-1,1)`. -/
theorem dens_tendsto {u : ℝ} (hu : u ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun l : ℝ => dens l u) (𝓝 0) (𝓝 (dens 0 u)) := by
  have hb : 0 < 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  simp only [dens, if_pos hu]
  apply Tendsto.mul
  · unfold cl
    apply Tendsto.div
    · exact (Real.differentiableAt_Gamma (by intro m; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
        |>.continuousAt).tendsto.comp (by
          simpa using (continuous_id.add continuous_const).continuousAt (x := (0:ℝ)) |>.tendsto)
    · apply Tendsto.const_mul
      exact (Real.differentiableAt_Gamma (by intro m; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
        |>.continuousAt).tendsto.comp (by
          simpa using (continuous_id.add continuous_const).continuousAt (x := (0:ℝ)) |>.tendsto)
    · have : 0 < Real.Gamma (0 + 1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
      exact (mul_pos (Real.sqrt_pos.mpr Real.pi_pos) this).ne'
  · exact ((Real.continuousAt_const_rpow hb.ne').comp
      ((continuous_id.sub continuous_const).continuousAt)).tendsto.congr (fun _ => rfl) |>.trans (by simp)

end GegenbauerFock.Manuscript13
