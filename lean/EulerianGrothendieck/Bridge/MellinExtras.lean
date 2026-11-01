import Bridge.Mellin
import Bridge.Rabotnov
import EulerianGrothendieck.GaussianFockBridge
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Sections 6 and 8: remaining statements

* Proposition 6.2 (rest): `q_E > 0`, strictly decreasing on `t > 0`, `q_E(t) ≤ 2e^{-|t|}`;
* Corollary 6.4: `d_E = 1/∫t²q_E = 1/(4β(3)) = 1/(4[-(7/8)ζ(3) - ψ''(1/4)/64]) = 8/π³` and
  `r_E(π) = (∫ t² q_E)^{-1/3}`;
* Corollary 6.5: `β(2) = (1/2)∫ t q_E`, `ζ(3) = (8/9)∫ t³ q_E²`;
* Proposition 6.7, from the cited Fourier integral `∫ sech(πx/2) e^{itx} dx = 2 sech t`
  (Gradshteyn–Ryzhik 3.981.3, a hypothesis): the density representation, unit mass and
  positive definiteness of `q_E`;
* Proposition 8.1 (rest): `F_E` is entire and `F_E(w²) = w² r_E(iw)`.
-/

open Real MeasureTheory Set Filter Topology

namespace EulerianBridge.MellinExtras

open EulerianBridge.Mellin

/-! ## Proposition 6.2 -/

theorem qE_pos (t : ℝ) : 0 < qE t := by
  rw [(qE_eq_sech t).1, sech]; exact one_div_pos.mpr (cosh_pos t)

theorem qE_strictAntiOn : StrictAntiOn qE (Ioi 0) := by
  intro a ha b hb hab
  rw [(qE_eq_sech a).1, (qE_eq_sech b).1, sech, sech]
  apply one_div_lt_one_div_of_lt (cosh_pos a)
  rw [cosh_lt_cosh, abs_of_pos (mem_Ioi.mp ha), abs_of_pos (mem_Ioi.mp hb)]; exact hab

theorem qE_le_exp (t : ℝ) : qE t ≤ 2 * exp (-|t|) := by
  rw [(qE_eq_sech t).1, sech, cosh_eq]
  have hge : exp |t| ≤ exp t + exp (-t) := by
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]; linarith [exp_pos (-t)]
    · rw [abs_of_nonpos h]; linarith [exp_pos t]
  rw [one_div_div, exp_neg |t|, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (by norm_num) (exp_pos _) hge

/-! ## Corollaries 6.4 and 6.5 -/

/-- `r_E(π) = 2/π` for the Eulerian entire function. -/
theorem rE_pi : EulerianGrothendieck.Fock.rE (π : ℂ) = ((2 / π : ℝ) : ℂ) := by
  rw [EulerianGrothendieck.Fock.rE_eq_sin_div (by exact_mod_cast pi_ne_zero)]
  rw [show (π : ℂ) / 2 = ((π / 2 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sin, sin_pi_div_two]
  have : (π : ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  push_cast
  field_simp

/-- Corollary 6.4, eq. (159). -/
theorem det_mellin :
    let I₂ := ∫ t in Ioi (0:ℝ), t ^ 2 * qE t
    8 / π ^ 3 = 1 / I₂ ∧ 1 / I₂ = 1 / (4 * dirichletBeta 3) ∧
      1 / (4 * dirichletBeta 3) = 1 / (4 * (-(7 / 8) * zeta 3 - psi2Quarter / 64)) := by
  intro I₂
  have hI : I₂ = 4 * dirichletBeta 3 := moment_two.1
  have hI' : 4 * dirichletBeta 3 = π ^ 3 / 8 := moment_two.2
  refine ⟨?_, by rw [hI], by rw [beta_three_polygamma]⟩
  rw [hI, hI']; field_simp

/-- Corollary 6.4, eq. (160): `r_E(π) = (∫ t² q_E)^{-1/3}`. -/
theorem radius_mellin :
    (2 / π : ℝ) = 1 / (∫ t in Ioi (0:ℝ), t ^ 2 * qE t) ^ ((1:ℝ) / 3) := by
  rw [moment_two.1, moment_two.2]
  have hp : 0 < π := pi_pos
  have hcube : (π ^ 3 / 8) ^ ((1:ℝ) / 3) = π / 2 := by
    rw [show π ^ 3 / 8 = (π / 2) ^ (3:ℕ) by ring, ← rpow_natCast, ← rpow_mul (by positivity)]
    norm_num
  rw [hcube]; field_simp

/-- Corollary 6.5, eqs. (161)–(162). -/
theorem two_constants :
    dirichletBeta 2 = 1 / 2 * ∫ t in Ioi (0:ℝ), t * qE t ∧
      zeta 3 = 8 / 9 * ∫ t in Ioi (0:ℝ), t ^ 3 * qE t ^ 2 := by
  rw [moment_one, moment_three_sq]; constructor <;> ring

/-! ## Proposition 6.7 -/

/-- The cited Fourier integral (Gradshteyn–Ryzhik, entry 3.981.3). -/
def SechFourier : Prop :=
  ∀ t : ℝ, ∫ x : ℝ, (Real.cosh (π * x / 2))⁻¹ * Complex.exp (Complex.I * t * x) = 2 * (Real.cosh t : ℂ)⁻¹

/-- The probability density `ρ(x) = (1/2) sech(πx/2)`. -/
noncomputable def ρ (x : ℝ) : ℝ := 1 / 2 * (Real.cosh (π * x / 2))⁻¹

/-- Eq. (163): `q_E(t) = ∫ e^{itx} ρ(x) dx`. -/
theorem qE_characteristic (h : SechFourier) (t : ℝ) :
    (qE t : ℂ) = ∫ x : ℝ, Complex.exp (Complex.I * t * x) * (ρ x : ℂ) := by
  have ht := h t
  rw [(qE_eq_sech t).1, sech]
  have e : ∀ x : ℝ, Complex.exp (Complex.I * t * x) * (ρ x : ℂ)
      = (1 / 2 : ℂ) * ((Real.cosh (π * x / 2))⁻¹ * Complex.exp (Complex.I * t * x)) := by
    intro x; unfold ρ; push_cast; ring
  simp_rw [e]
  rw [integral_const_mul, ht]; push_cast; ring

theorem integrable_ρ (h : SechFourier) :
    Integrable (fun x : ℝ => (((Real.cosh (π * x / 2))⁻¹ : ℝ) : ℂ)) := by
  have h0 := h 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Real.cosh_zero,
    Complex.ofReal_one, inv_one] at h0
  by_contra hni
  rw [integral_undef hni] at h0
  norm_num at h0

/-- The density has unit mass. -/
theorem integral_ρ (h : SechFourier) : ∫ x : ℝ, ρ x = 1 := by
  have h0 := h 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, mul_one, Real.cosh_zero,
    Complex.ofReal_one, inv_one] at h0
  have e : ∀ x : ℝ, ((ρ x : ℝ) : ℂ) = (1 / 2 : ℂ) * (((Real.cosh (π * x / 2))⁻¹ : ℝ) : ℂ) := by
    intro x; unfold ρ; rw [Complex.ofReal_mul]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have : ((∫ x : ℝ, ρ x : ℝ) : ℂ) = 1 := by
    rw [← integral_complex_ofReal]
    simp_rw [e]
    rw [integral_const_mul, h0]; norm_num
  exact_mod_cast this

/-- Positive definiteness: `∑_{j,k} c_j \bar c_k q_E(t_j - t_k) = ∫ |∑_j c_j e^{i t_j x}|² ρ(x) dx ≥ 0`. -/
theorem qE_posDef (h : SechFourier) {n : ℕ} (t : Fin n → ℝ) (c : Fin n → ℂ) :
    ∑ j, ∑ k, c j * starRingEnd ℂ (c k) * (qE (t j - t k) : ℂ) =
      ((∫ x : ℝ, ‖∑ j, c j * Complex.exp (Complex.I * t j * x)‖ ^ 2 * ρ x : ℝ) : ℂ) ∧
    0 ≤ ∫ x : ℝ, ‖∑ j, c j * Complex.exp (Complex.I * t j * x)‖ ^ 2 * ρ x := by
  have hint := integrable_ρ h
  have hintρ : Integrable (fun x : ℝ => (ρ x : ℂ)) := by
    have := hint.const_mul (1 / 2 : ℂ); refine this.congr (Eventually.of_forall (fun x => ?_))
    simp only [ρ, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  refine ⟨?_, integral_nonneg (fun x => mul_nonneg (by positivity)
    (by unfold ρ; exact mul_nonneg (by norm_num) (inv_nonneg.mpr (cosh_pos _).le)))⟩
  rw [← integral_complex_ofReal]
  have hsq : ∀ x : ℝ, (((‖∑ j, c j * Complex.exp (Complex.I * t j * x)‖ ^ 2 * ρ x : ℝ)) : ℂ) =
      ∑ j, ∑ k, c j * starRingEnd ℂ (c k) *
        (Complex.exp (Complex.I * ((t j - t k : ℝ) : ℂ) * x) * (ρ x : ℂ)) := by
    intro x
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul,
      Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_mul, ← Complex.exp_conj]
    have : starRingEnd ℂ (Complex.I * (t k : ℂ) * (x : ℂ)) = -(Complex.I * (t k : ℂ) * (x : ℂ)) := by
      simp [Complex.conj_ofReal]
    rw [this]
    push_cast
    have e : Complex.exp (Complex.I * ((t j : ℂ) - t k) * x) =
        Complex.exp (Complex.I * t j * x) * Complex.exp (-(Complex.I * t k * x)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [e]; ring
  have hik : ∀ j k, Integrable (fun x : ℝ => c j * starRingEnd ℂ (c k) *
      (Complex.exp (Complex.I * ((t j - t k : ℝ) : ℂ) * x) * (ρ x : ℂ))) := by
    intro j k
    refine Integrable.const_mul ?_ _
    refine hintρ.bdd_mul (f := fun x : ℝ => Complex.exp (Complex.I * ((t j - t k : ℝ) : ℂ) * x))
      (Continuous.aestronglyMeasurable (by fun_prop)) ⟨1, fun x => ?_⟩
    rw [Complex.norm_exp]; simp
  simp_rw [hsq]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hik j k))]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integral_finset_sum _ (fun k _ => hik j k)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [integral_const_mul, ← qE_characteristic h]

/-! ## Proposition 8.1: `F_E` is entire -/

open EulerianBridge.Rabotnov

theorem c_ne_zero {n : ℕ} (hn : 1 ≤ n) : c n ≠ 0 := by
  unfold c
  rw [if_neg (by omega)]
  have h1 : (4:ℂ) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : ((2 * n - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  exact one_div_ne_zero (mul_ne_zero h1 h2)

theorem c_ratio {n : ℕ} (hn : 1 ≤ n) : ‖c (n + 1)‖ / ‖c n‖ = 1 / (4 * (2 * n) * (2 * n + 1)) := by
  unfold c
  rw [if_neg (by omega), if_neg (by omega), show n + 1 - 1 = (n - 1) + 1 by omega,
    show 2 * (n + 1) - 1 = (2 * n - 1) + 2 by omega, Nat.factorial_succ, Nat.factorial_succ]
  have hf : (0:ℝ) < (2 * n - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  simp only [norm_div, norm_one, norm_mul, norm_pow, Complex.norm_natCast, Complex.norm_ofNat]
  have hc : ((2 * n - 1 : ℕ) : ℝ) = 2 * n - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  push_cast
  rw [hc]
  have h4 : (0:ℝ) < 4 ^ (n - 1) := by positivity
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have h2n : (2 * (n:ℝ) + 1) ≠ 0 := by positivity
  have h2n' : (1 + 2 * (n:ℝ)) ≠ 0 := by positivity
  rw [pow_succ, show (2 * (n:ℝ) - 1 + 1 + 1) = 2 * n + 1 by ring, show (2 * (n:ℝ) - 1 + 1) = 2 * n by ring]
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  field_simp

theorem radius_FE : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · filter_upwards [eventually_ge_atTop 1] with n hn using c_ne_zero hn
  · have h : Tendsto (fun n : ℕ => 1 / (4 * (2 * (n:ℝ)) * (2 * n + 1))) atTop (𝓝 0) := by
      apply Tendsto.div_atTop tendsto_const_nhds
      apply Tendsto.atTop_mul_atTop₀ _ (tendsto_atTop_add_const_right _ 1
        ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num)))
      exact ((tendsto_natCast_atTop_atTop).const_mul_atTop (by norm_num : (0:ℝ) < 2)).const_mul_atTop
        (by norm_num)
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [c_ratio hn]

theorem FE_eq_ofScalarsSum : FE = FormalMultilinearSeries.ofScalarsSum c := by
  funext z
  rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  unfold FE
  simp [smul_eq_mul]

/-- Proposition 8.1: `F_E` is entire. -/
theorem FE_differentiable : Differentiable ℂ FE := by
  rw [FE_eq_ofScalarsSum]
  have hb := (FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
    (by rw [radius_FE]; exact ENNReal.zero_lt_top)
  rw [radius_FE] at hb
  intro z
  have := hb.analyticAt_of_mem (y := z) (by simp)
  exact this.differentiableAt

/-- Eq. (170): `F_E(w²) = w² r_E(iw)`. -/
theorem FE_eq_rE (w : ℂ) : FE (w ^ 2) = w ^ 2 * EulerianGrothendieck.Fock.rE (Complex.I * w) := by
  rw [FE_eq_sq]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  rw [EulerianGrothendieck.Fock.rE_eq_sin_div (mul_ne_zero Complex.I_ne_zero hw),
    show Complex.I * w / 2 = (w / 2) * Complex.I by ring, Complex.sin_mul_I]
  field_simp

end EulerianBridge.MellinExtras
