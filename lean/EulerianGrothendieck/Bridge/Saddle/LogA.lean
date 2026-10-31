import Bridge.Saddle.Fourier
import Bridge.Saddle.Cauchy
import Bridge.Saddle.ULLambda
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inverse

/-!
# Lemma 5.5, part 6: `Λ = log A`, its derivatives `κ_r`, and the saddlepoint `s(x)`

Manuscript V173, eqs. (55)–(56) and (73).

* `Lc = log ∘ A` is holomorphic on `U = {Re A > 0}`, an open set containing `ℝ`;
  `κc n = Lc^{(n)}` (complex) and `κ n = Λ^{(n)}` (real), with `κc n s = κ n s` on `ℝ`
  (`κc_ofReal`) and `κ_n' = κ_{n+1}` (`hasDerivAt_κ`);
* `κ_one_eq_Lp`: `κ_1 = Λ'` is the explicit function `1/2 + 1/(eˢ-1) - 1/s` of Lemma 5.3;
  `κ_two_pos`: `κ_2 = Λ'' > 0`, with `κ_2(0) = 1/12`;
* `hasDerivAt_Ip`: the inverse `s = I'` of `Λ'` satisfies `s' = 1/κ_2(s)`;
* uniform Cauchy estimates on `[-σ, σ]` (`coeff_bound`, `taylor_Lc`), the input for (73).
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-! ## The holomorphic logarithm of `A` -/

/-- The domain `{z : Re A(z) > 0}`. -/
def Udom : Set ℂ := {z | 0 < (A z).re}

theorem isOpen_Udom : IsOpen Udom :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_A)

theorem ofReal_mem_Udom (s : ℝ) : (s:ℂ) ∈ Udom := by
  show 0 < (A s).re
  rw [A_ofReal, Complex.ofReal_re]; exact Ar_pos s

/-- `Λ_c(z) = log A(z)` (principal branch). -/
noncomputable def Lc (z : ℂ) : ℂ := Complex.log (A z)

theorem differentiableOn_Lc : DifferentiableOn ℂ Lc Udom := fun z hz =>
  ((differentiable_A z).clog (Or.inl hz)).differentiableWithinAt

theorem analyticOnNhd_Lc : AnalyticOnNhd ℂ Lc Udom :=
  differentiableOn_Lc.analyticOnNhd isOpen_Udom

/-- `κc n = Λ_c^{(n)}`. -/
noncomputable def κc (n : ℕ) : ℂ → ℂ := iteratedDeriv n Lc

theorem analyticOnNhd_κc (n : ℕ) : AnalyticOnNhd ℂ (κc n) Udom := by
  have h := analyticOnNhd_Lc.iterated_deriv n
  have heq : κc n = deriv^[n] Lc := by funext z; simp [κc, iteratedDeriv_eq_iterate]
  rw [heq]; exact h

theorem hasDerivAt_κc (n : ℕ) {z : ℂ} (hz : z ∈ Udom) : HasDerivAt (κc n) (κc (n + 1) z) z := by
  have hd := ((analyticOnNhd_κc n) z hz).differentiableAt.hasDerivAt
  have : deriv (κc n) z = κc (n + 1) z := by
    show deriv (iteratedDeriv n Lc) z = iteratedDeriv (n + 1) Lc z
    rw [iteratedDeriv_succ]
  rwa [this] at hd

theorem κc_zero : κc 0 = Lc := by funext z; simp [κc]

theorem exp_Lc {z : ℂ} (hz : z ∈ Udom) : cexp (Lc z) = A z := by
  rw [Lc, Complex.exp_log]
  intro h; have : (A z).re = 0 := by rw [h]; simp
  exact absurd hz (by simp [Udom, this])

/-! ## The real cumulant function -/

/-- `Λ(s) = log A(s) = log(sinh(s/2)/(s/2))`. -/
noncomputable def Lr (s : ℝ) : ℝ := Real.log (Ar s)

theorem Lc_ofReal (s : ℝ) : Lc s = (Lr s : ℂ) := by
  rw [Lc, A_ofReal, Lr, Complex.ofReal_log (Ar_pos s).le]

/-- `κ n = Λ^{(n)}`. -/
noncomputable def κ (n : ℕ) : ℝ → ℝ := iteratedDeriv n Lr

theorem iteratedDeriv_Lr : ∀ n : ℕ, iteratedDeriv n Lr = fun s : ℝ => (κc n (s:ℂ)).re
  | 0 => by funext s; simp [κc, Lc_ofReal]
  | (n + 1) => by
      rw [iteratedDeriv_succ, iteratedDeriv_Lr n]
      funext s
      exact ((hasDerivAt_κc n (ofReal_mem_Udom s)).real_of_complex).deriv

theorem κc_ofReal_im : ∀ (n : ℕ) (s : ℝ), (κc n s).im = 0
  | 0, s => by rw [κc_zero, Lc_ofReal]; simp
  | (n + 1), s => by
      have h := (hasDerivAt_κc n (ofReal_mem_Udom s)).comp_ofReal
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h
      have h0 : (fun t : ℝ => Complex.imCLM (κc n t)) = fun _ => (0:ℝ) := by
        funext t; simp [κc_ofReal_im n t]
      rw [Function.comp_def, h0] at him
      have := him.unique (hasDerivAt_const s (0:ℝ))
      simpa using this

theorem κc_ofReal (n : ℕ) (s : ℝ) : κc n s = (κ n s : ℂ) := by
  apply Complex.ext
  · show (κc n s).re = iteratedDeriv n Lr s
    rw [iteratedDeriv_Lr]
  · simp [κc_ofReal_im]

theorem κ_eq (n : ℕ) : κ n = fun s : ℝ => (κc n (s:ℂ)).re := iteratedDeriv_Lr n

theorem hasDerivAt_κ (n : ℕ) (s : ℝ) : HasDerivAt (κ n) (κ (n + 1) s) s := by
  rw [κ_eq n, κ_eq (n + 1)]
  exact (hasDerivAt_κc n (ofReal_mem_Udom s)).real_of_complex

theorem continuous_κ (n : ℕ) : Continuous (κ n) :=
  continuous_iff_continuousAt.mpr fun s => (hasDerivAt_κ n s).continuousAt

theorem κ_zero_eq (s : ℝ) : κ 0 s = Lr s := by simp [κ]

/-! ## `κ_1 = Λ'` and `κ_2 = Λ'' > 0` -/

theorem Ak_one_zero : Ak 1 0 = 0 := by
  simp only [Ak, zero_mul, Complex.exp_zero, mul_one, pow_one]
  rw [intervalIntegral.integral_ofReal, integral_id]; norm_num

theorem Ak_two_zero : Ak 2 0 = 1 / 12 := by
  simp only [Ak, zero_mul, Complex.exp_zero, mul_one]
  have : ∫ t in (-1/2:ℝ)..(1/2), ((t:ℂ)) ^ 2 = ((∫ t in (-1/2:ℝ)..(1/2), t ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
  rw [this, integral_pow]; norm_num

theorem hasDerivAt_Lc {z : ℂ} (hz : z ∈ Udom) : HasDerivAt Lc (Ak 1 z / A z) z :=
  (hasDerivAt_A z).clog (Or.inl hz)

theorem κc_one_eq {z : ℂ} (hz : z ∈ Udom) : κc 1 z = Ak 1 z / A z := by
  rw [κc, iteratedDeriv_one]; exact (hasDerivAt_Lc hz).deriv

theorem κc_two_eq {z : ℂ} (hz : z ∈ Udom) :
    κc 2 z = (Ak 2 z * A z - Ak 1 z * Ak 1 z) / A z ^ 2 := by
  have hev : κc 1 =ᶠ[𝓝 z] fun z => Ak 1 z / A z := by
    filter_upwards [isOpen_Udom.mem_nhds hz] with y hy
    exact κc_one_eq hy
  have hAz : A z ≠ 0 := by
    intro h; have : (A z).re = 0 := by rw [h]; simp
    exact absurd hz (by simp [Udom, this])
  have hd := (hasDerivAt_Ak 1 z).div (hasDerivAt_A z) hAz
  have h2 : κc 2 z = deriv (κc 1) z := by
    show iteratedDeriv (1 + 1) Lc z = deriv (iteratedDeriv 1 Lc) z
    rw [iteratedDeriv_succ]
  rw [h2, hev.deriv_eq]
  exact hd.deriv

theorem κ_one_zero : κ 1 0 = 0 := by
  rw [κ_eq]; simp only
  rw [show ((0:ℝ):ℂ) = 0 by simp, κc_one_eq (by simpa using ofReal_mem_Udom 0), Ak_one_zero]
  simp

theorem κ_two_zero : κ 2 0 = 1 / 12 := by
  rw [κ_eq]; simp only
  rw [show ((0:ℝ):ℂ) = 0 by simp, κc_two_eq (by simpa using ofReal_mem_Udom 0), Ak_one_zero,
    Ak_two_zero, A_zero]
  norm_num

theorem hasDerivAt_Lr_closed {s : ℝ} (hs : s ≠ 0) : HasDerivAt Lr (UL.Lp s) s := by
  set g : ℝ → ℝ := fun x => (Real.exp (x / 2) - Real.exp (-x / 2)) / x
  have hev : (fun x => Real.log (g x)) =ᶠ[𝓝 s] Lr := by
    filter_upwards [isOpen_ne.mem_nhds hs] with x hx
    simp only [g, Lr, Ar_eq_closed hx]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have hgs : g s = Ar s := (Ar_eq_closed hs).symm
  have hg0 : g s ≠ 0 := by rw [hgs]; exact (Ar_pos s).ne'
  have h1 : HasDerivAt (fun x => Real.exp (x / 2) - Real.exp (-x / 2))
      (Real.exp (s / 2) / 2 + Real.exp (-s / 2) / 2) s := by
    have ha := ((hasDerivAt_id s).div_const 2).exp
    have hb := ((hasDerivAt_id s).neg.div_const 2).exp
    convert ha.sub hb using 1
    simp only [id, Pi.neg_apply]; ring_nf
  have h2 : HasDerivAt g (((Real.exp (s / 2) / 2 + Real.exp (-s / 2) / 2) * s -
      (Real.exp (s / 2) - Real.exp (-s / 2))) / s ^ 2) s :=
    (h1.div (hasDerivAt_id s) hs).congr_deriv (by simp only [id_eq, mul_one])
  have h3 := h2.log hg0
  convert h3 using 1
  rw [UL.Lp_of_ne hs]
  simp only [g]
  have he := Real.exp_pos (s / 2)
  have hneg : Real.exp (-s / 2) = (Real.exp (s / 2))⁻¹ := by rw [← Real.exp_neg]; ring_nf
  have hsq : Real.exp s = Real.exp (s / 2) ^ 2 := UL.exp_eq_sq_half s
  have hg0' := hg0
  simp only [g] at hg0'
  rw [hneg, hsq]
  rw [hneg] at hg0'
  set e := Real.exp (s / 2)
  have hne : e - e⁻¹ ≠ 0 := by
    intro h; apply hg0'; rw [h, zero_div]
  have he' : e ≠ 0 := he.ne'
  have hne2 : e ^ 2 - 1 ≠ 0 := by
    intro h; apply hne
    have : e * (e - e⁻¹) = e ^ 2 - 1 := by field_simp
    rw [h] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' he'
    · exact h'
  field_simp
  ring

theorem κ_one_eq_Lp : κ 1 = UL.Lp := by
  funext s
  by_cases hs : s = 0
  · subst hs; rw [κ_one_zero, UL.Lp_zero]
  · rw [κ, iteratedDeriv_one]; exact (hasDerivAt_Lr_closed hs).deriv

theorem Lpp_neg (s : ℝ) : UL.Lpp (-s) = UL.Lpp s := by
  unfold UL.Lpp
  rw [neg_sq]
  congr 1
  by_cases hs : s = 0
  · subst hs; simp
  have he := UL.exp_sub_one_ne hs
  have he' := UL.exp_sub_one_ne (neg_ne_zero.mpr hs)
  rw [Real.exp_neg] at he' ⊢
  have hpos := Real.exp_pos s
  rw [div_eq_div_iff (pow_ne_zero 2 he') (pow_ne_zero 2 he)]
  field_simp
  ring

theorem κ_two_pos (s : ℝ) : 0 < κ 2 s := by
  by_cases hs : s = 0
  · subst hs; rw [κ_two_zero]; norm_num
  · have h1 := hasDerivAt_κ 1 s
    rw [κ_one_eq_Lp] at h1
    have h2 := UL.hasDerivAt_Lp hs
    rw [h1.unique h2]
    rcases lt_or_gt_of_ne hs with h | h
    · rw [← Lpp_neg]; exact UL.Lpp_pos (by linarith)
    · exact UL.Lpp_pos h

/-! ## The saddlepoint `s(x) = I'(x)` -/

theorem Lp_Ip' {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : κ 1 (UL.Ip x) = x := by
  rw [κ_one_eq_Lp]; exact UL.Lp_Ip hx

theorem hasDerivAt_Ip {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt UL.Ip (κ 2 (UL.Ip x))⁻¹ x := by
  have hc : ContinuousAt UL.Ip x := UL.Ip_continuousOn.continuousAt (Ioo_mem_nhds hx.1 hx.2)
  have hf := hasDerivAt_κ 1 (UL.Ip x)
  rw [κ_one_eq_Lp] at hf
  refine HasDerivAt.of_local_left_inverse hc hf (κ_two_pos _).ne' ?_
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  exact UL.Lp_Ip hy

/-! ## Uniform Cauchy estimates near `[-σ, σ]` -/

/-- Radius of the Cauchy discs. -/
noncomputable def Rσ (σ : ℝ) : ℝ := Real.exp (-σ / 2) / 2

/-- Uniform bound for `Λ_c` on the Cauchy discs. -/
noncomputable def Bσ (σ : ℝ) : ℝ := Real.log 2 + (σ + 1) / 2 + Real.pi

theorem Rσ_pos (σ : ℝ) : 0 < Rσ σ := by unfold Rσ; positivity

theorem Rσ_le_half {σ : ℝ} (hσ : 0 ≤ σ) : Rσ σ ≤ 1 / 2 := by
  unfold Rσ
  have : Real.exp (-σ / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem re_A_ge {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) {z : ℂ} (hz : ‖z - s‖ ≤ Rσ σ) :
    1 / 2 ≤ (A z).re := by
  have h1 : ‖z - s‖ ≤ 1 := hz.trans ((Rσ_le_half hσ).trans (by norm_num))
  have h2 := norm_A_sub s h1
  have h3 : Real.exp (|s| / 2) * ‖z - s‖ ≤ 1 / 2 := by
    calc Real.exp (|s| / 2) * ‖z - s‖ ≤ Real.exp (σ / 2) * Rσ σ :=
          mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hz (norm_nonneg _) (Real.exp_pos _).le
      _ = 1 / 2 := by
          unfold Rσ; rw [mul_div_assoc', ← Real.exp_add]; simp [show σ / 2 + -σ / 2 = 0 by ring]
  have h4 : (A s).re - (A z).re ≤ ‖A z - A s‖ := by
    have := Complex.abs_re_le_norm (A z - A s)
    rw [Complex.sub_re] at this
    linarith [neg_abs_le ((A z).re - (A s).re)]
  have h5 : (A s).re = Ar s := by rw [A_ofReal]; simp
  linarith [one_le_Ar s]

theorem mem_Udom_of {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) {z : ℂ} (hz : z ∈ closedBall (s:ℂ) (Rσ σ)) :
    z ∈ Udom := by
  rw [mem_closedBall, dist_eq_norm] at hz
  show 0 < (A z).re
  linarith [re_A_ge hσ hs hz]

theorem norm_Lc_le {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) {z : ℂ}
    (hz : z ∈ closedBall (s:ℂ) (Rσ σ)) : ‖Lc z‖ ≤ Bσ σ := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := re_A_ge hσ hs hz
  have hlow : 1 / 2 ≤ ‖A z‖ := hre.trans (Complex.re_le_norm _)
  have hzre : |z.re| ≤ σ + 1 / 2 := by
    have h1 : |z.re - s| ≤ ‖z - s‖ := by
      have := Complex.abs_re_le_norm (z - s); simpa using this
    have h2 := Rσ_le_half hσ
    have h3 := abs_sub_abs_le_abs_sub z.re s
    linarith
  have hup : ‖A z‖ ≤ Real.exp ((σ + 1) / 2) :=
    (norm_A_le_exp z).trans (Real.exp_le_exp.mpr (by linarith))
  have hApos : 0 < ‖A z‖ := by linarith
  have hlog : |Real.log ‖A z‖| ≤ Real.log 2 + (σ + 1) / 2 := by
    rw [abs_le]
    constructor
    · have : Real.log (1 / 2) ≤ Real.log ‖A z‖ := Real.log_le_log (by norm_num) hlow
      rw [one_div, Real.log_inv] at this
      have : 0 ≤ (σ + 1) / 2 := by linarith
      linarith
    · have : Real.log ‖A z‖ ≤ Real.log (Real.exp ((σ + 1) / 2)) := Real.log_le_log hApos hup
      rw [Real.log_exp] at this
      have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
  calc ‖Lc z‖ ≤ |(Lc z).re| + |(Lc z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖A z‖| + |Complex.arg (A z)| := by rw [Lc, Complex.log_re, Complex.log_im]
    _ ≤ (Real.log 2 + (σ + 1) / 2) + Real.pi := add_le_add hlog (Complex.abs_arg_le_pi _)
    _ = Bσ σ := rfl

theorem differentiableOn_Lc_ball {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) :
    DifferentiableOn ℂ Lc (closedBall (s:ℂ) (Rσ σ)) :=
  differentiableOn_Lc.mono (fun z hz => mem_Udom_of hσ hs hz)

/-- Cauchy bound for the Taylor coefficients `κ_n(s)/n!`, uniform in `|s| ≤ σ`. -/
theorem coeff_bound {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) (n : ℕ) :
    ‖((n ! : ℂ))⁻¹ * κc n s‖ ≤ Bσ σ / Rσ σ ^ n :=
  cauchy_coeff_bound (Rσ_pos σ) (differentiableOn_Lc_ball hσ hs)
    (fun z hz => norm_Lc_le hσ hs hz) n

theorem abs_κ_le {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) (n : ℕ) :
    |κ n s| ≤ n ! * (Bσ σ / Rσ σ ^ n) := by
  have h := norm_iteratedDeriv_le (Rσ_pos σ) (differentiableOn_Lc_ball hσ hs)
    (fun z hz => norm_Lc_le hσ hs hz) n
  have : ‖iteratedDeriv n Lc (s:ℂ)‖ = |κ n s| := by
    rw [show iteratedDeriv n Lc (s:ℂ) = κc n s from rfl, κc_ofReal, Complex.norm_real,
      Real.norm_eq_abs]
  rw [this] at h; exact h

/-- Taylor remainder for `Λ_c` at `s`, uniform in `|s| ≤ σ`. -/
theorem taylor_Lc {σ s : ℝ} (hσ : 0 ≤ σ) (hs : |s| ≤ σ) (N : ℕ) {w : ℂ} (hw : ‖w‖ ≤ Rσ σ / 2) :
    ‖Lc (s + w) - ∑ n ∈ Finset.range N, ((n ! : ℂ))⁻¹ * κc n s * w ^ n‖ ≤
      2 * Bσ σ * (‖w‖ / Rσ σ) ^ N :=
  taylor_remainder_bound (Rσ_pos σ) (differentiableOn_Lc_ball hσ hs)
    (fun z hz => norm_Lc_le hσ hs hz) N hw

/-- `κ_2` is bounded below on `[-σ, σ]`. -/
theorem exists_κ_two_lower (σ : ℝ) : ∃ c > 0, ∀ s, |s| ≤ σ → c ≤ κ 2 s := by
  by_cases hσ : 0 ≤ σ
  · obtain ⟨s0, hs0, hmin⟩ := (isCompact_Icc (a := -σ) (b := σ)).exists_isMinOn
      (nonempty_Icc.mpr (by linarith)) (continuous_κ 2).continuousOn
    refine ⟨κ 2 s0, κ_two_pos s0, fun s hs => ?_⟩
    exact hmin (mem_Icc.mpr (abs_le.mp hs))
  · refine ⟨1, one_pos, fun s hs => ?_⟩
    exact absurd ((abs_nonneg s).trans hs) hσ

end EulerianBridge.Saddle
