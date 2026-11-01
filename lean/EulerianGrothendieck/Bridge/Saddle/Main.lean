import Bridge.Saddle.FinalAlg

/-!
# Lemma 5.5 (manuscript V173): the saddlepoint estimate with two derivatives

For every `b ∈ (0, 1/2)` there are `M₀` and `C` such that for `M ≥ M₀`
`‖log g_M + MI - ½ log(M/(2πv)) - η/M‖_{C²([-b,b])} ≤ C/(M√M)`  (eq. (115)), `lemma_5_5`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-! ## Oddness and range of `s(x)` -/

theorem Ip_neg {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : UL.Ip (-x) = -UL.Ip x := by
  have h := UL.Lp_Ip hx
  have : UL.Lp (-UL.Ip x) = -x := by rw [UL.Lp_odd, h]
  rw [← this, UL.Ip_Lp]

theorem abs_Ip_le {b y : ℝ} (hb : b < 1 / 2) (hy : |y| ≤ b) : |UL.Ip y| ≤ UL.Ip b := by
  have hb0 : 0 ≤ b := (abs_nonneg y).trans hy
  have hbI : b ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, hb⟩
  have hmono := UL.Ip_strictMonoOn.monotoneOn
  rcases le_or_lt 0 y with h | h
  · have hyI : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith [abs_of_nonneg h ▸ hy]⟩
    rw [abs_of_nonneg (UL.Ip_nonneg h (by linarith [abs_of_nonneg h ▸ hy]))]
    exact hmono hyI hbI (by linarith [abs_of_nonneg h ▸ hy])
  · have hy' : -y ≤ b := by rw [abs_of_neg h] at hy; linarith
    have hyI : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith⟩
    have hnI : -y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith, by linarith⟩
    have h1 : UL.Ip y = -UL.Ip (-y) := by rw [Ip_neg hyI, neg_neg]
    have h2 : 0 ≤ UL.Ip (-y) := UL.Ip_nonneg (by linarith) (by linarith)
    rw [h1, abs_neg, abs_of_nonneg h2]
    exact hmono hnI hbI hy'

/-! ## Continuity of the coefficients -/

theorem continuous_div_κ2 {f : ℝ → ℝ} (hf : Continuous f) (k : ℕ) :
    Continuous fun s => f s / κ 2 s ^ k :=
  hf.div ((continuous_κ 2).pow k) (fun s => pow_ne_zero k (κ2_ne s))

theorem continuous_etaS : Continuous etaS := by
  unfold etaS
  have h1 := continuous_div_κ2 (continuous_κ 4) 2
  have h2 := continuous_div_κ2 ((continuous_κ 3).pow 2) 3
  have : (fun s => (κ 4 s / κ 2 s ^ 2 - 5 * κ 3 s ^ 2 / (3 * κ 2 s ^ 3)) / 8) =
      fun s => (κ 4 s / κ 2 s ^ 2 - 5 / 3 * (κ 3 s ^ 2 / κ 2 s ^ 3)) / 8 := by
    funext s; have := κ2_ne s; field_simp
  rw [this]; fun_prop

theorem continuous_etaS1 : Continuous etaS1 := by
  unfold etaS1
  have h1 := continuous_div_κ2 (continuous_κ 5) 2
  have h2 := continuous_div_κ2 ((continuous_κ 3).mul (continuous_κ 4)) 3
  have h3 := continuous_div_κ2 ((continuous_κ 3).pow 3) 4
  have : (fun s => (κ 5 s / κ 2 s ^ 2 - 16 / 3 * κ 3 s * κ 4 s / κ 2 s ^ 3 + 5 * κ 3 s ^ 3 / κ 2 s ^ 4) / 8) =
      fun s => (κ 5 s / κ 2 s ^ 2 - 16 / 3 * (κ 3 s * κ 4 s / κ 2 s ^ 3) + 5 * (κ 3 s ^ 3 / κ 2 s ^ 4)) / 8 := by
    funext s; ring
  rw [this]; fun_prop

theorem continuous_etaS2 : Continuous etaS2 := by
  unfold etaS2
  have c2 := continuous_κ 2; have c3 := continuous_κ 3; have c4 := continuous_κ 4
  have c5 := continuous_κ 5; have c6 := continuous_κ 6
  have h1 := continuous_div_κ2 c6 2
  have h2 := continuous_div_κ2 (c5.mul c3) 3
  have h3 := continuous_div_κ2 ((c4.mul c4).add (c3.mul c5)) 3
  have h4 := continuous_div_κ2 ((c3.mul c4).mul c3) 4
  have h5 := continuous_div_κ2 ((c3.pow 2).mul c4) 4
  have h6 := continuous_div_κ2 ((c3.pow 3).mul c3) 5
  have : etaS2 = fun s => (κ 6 s / κ 2 s ^ 2 - 2 * (κ 5 s * κ 3 s / κ 2 s ^ 3)
      - 16 / 3 * ((κ 4 s * κ 4 s + κ 3 s * κ 5 s) / κ 2 s ^ 3 - 3 * (κ 3 s * κ 4 s * κ 3 s / κ 2 s ^ 4))
      + 5 * (3 * (κ 3 s ^ 2 * κ 4 s / κ 2 s ^ 4) - 4 * (κ 3 s ^ 3 * κ 3 s / κ 2 s ^ 5))) / 8 := by
    funext s; unfold etaS2; ring
  rw [show (fun s => (κ 6 s / κ 2 s ^ 2 - 2 * κ 5 s * κ 3 s / κ 2 s ^ 3
      - 16 / 3 * ((κ 4 s * κ 4 s + κ 3 s * κ 5 s) / κ 2 s ^ 3 - 3 * κ 3 s * κ 4 s * κ 3 s / κ 2 s ^ 4)
      + 5 * (3 * κ 3 s ^ 2 * κ 4 s / κ 2 s ^ 4 - 4 * κ 3 s ^ 3 * κ 3 s / κ 2 s ^ 5)) / 8) = etaS2 from rfl,
    this]
  fun_prop

theorem continuous_eta1 : Continuous eta1 := by
  unfold eta1; exact continuous_etaS1.div (continuous_κ 2) κ2_ne

theorem continuous_eta2 : Continuous eta2 := by
  unfold eta2
  have := (((continuous_etaS2.mul (continuous_κ 2)).sub (continuous_etaS1.mul (continuous_κ 3))).div
    ((continuous_κ 2).pow 2) (fun s => pow_ne_zero 2 (κ2_ne s)))
  exact this.div (continuous_κ 2) κ2_ne

theorem continuous_L1 : Continuous L1 := by
  unfold L1
  exact (continuous_κ 3).div (continuous_const.mul ((continuous_κ 2).pow 2))
    (fun s => mul_ne_zero (by norm_num) (pow_ne_zero 2 (κ2_ne s)))

theorem continuous_L2 : Continuous L2 := by
  unfold L2
  have c2 := continuous_κ 2; have c3 := continuous_κ 3; have c4 := continuous_κ 4
  have : Continuous fun s => κ 4 s * κ 2 s - 2 * κ 3 s ^ 2 := by fun_prop
  exact (this.div (continuous_const.mul ((continuous_κ 2).pow 3))
    (fun s => mul_ne_zero (by norm_num) (pow_ne_zero 3 (κ2_ne s)))).div (continuous_κ 2) κ2_ne

theorem continuous_ac (n : ℕ) : Continuous (ac n) := by
  have : ac n = fun s => ((κ n s / n ! : ℝ) : ℂ) := by funext s; exact ac_eq n s
  rw [this]; exact Complex.continuous_ofReal.comp ((continuous_κ n).div_const _)

theorem continuous_invkc (k : ℕ) : Continuous fun s => (1:ℂ) / kc s ^ k := by
  have : (fun s => (1:ℂ) / kc s ^ k) = fun s => ((1 / κ 2 s ^ k : ℝ) : ℂ) := by
    funext s; simp [kc]
  rw [this]
  exact Complex.continuous_ofReal.comp (continuous_div_κ2 continuous_const k)

theorem continuous_G04 : Continuous G04 := by
  have h : G04 = fun s => ac 6 s * (-15 * (1 / kc s ^ 3)) +
      (ac 3 s * ac 5 s + ac 4 s ^ 2 / 2) * (105 * (1 / kc s ^ 4)) +
      ac 3 s ^ 2 * ac 4 s / 2 * (-945 * (1 / kc s ^ 5)) + ac 3 s ^ 4 / 24 * (10395 * (1 / kc s ^ 6)) := by
    funext s; simp only [G04]; ring
  rw [h]
  have := continuous_ac 3; have := continuous_ac 4; have := continuous_ac 5; have := continuous_ac 6
  have := continuous_invkc 3; have := continuous_invkc 4; have := continuous_invkc 5
  have := continuous_invkc 6
  fun_prop

theorem exists_bound_on {σ : ℝ} {f : ℝ → ℂ} (hf : Continuous f) :
    ∃ K, ∀ s, |s| ≤ σ → ‖f s‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -σ) (b := σ)).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨K, fun s hs => hK s (mem_Icc.mpr (abs_le.mp hs))⟩

theorem cr (f : ℝ → ℝ) (hf : Continuous f) : Continuous fun s => ((f s : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp hf

/-- Uniform bounds for all coefficient functions on `[-σ, σ]`. -/
theorem exists_coeff_bound (σ : ℝ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ s, |s| ≤ σ →
    ‖G02 s‖ ≤ K ∧ ‖G04 s‖ ≤ K ∧ ‖G11 s‖ ≤ K ∧ ‖G13 s‖ ≤ K ∧ ‖G20 s‖ ≤ K ∧ ‖G22 s‖ ≤ K ∧
    ‖G24 s‖ ≤ K ∧ ‖(L2 s : ℂ)‖ ≤ K ∧ ‖(eta1 s : ℂ)‖ ≤ K ∧ ‖(eta2 s : ℂ)‖ ≤ K ∧ κ 2 s ≤ K := by
  have cG02 : Continuous G02 := by
    rw [show G02 = fun s => ((etaS s : ℝ) : ℂ) from funext id_G02]; exact cr _ continuous_etaS
  have cG11 : Continuous G11 := by
    rw [show G11 = fun s => ((L1 s : ℝ) : ℂ) from funext id_G11]; exact cr _ continuous_L1
  have cG13 : Continuous G13 := by
    rw [show G13 = fun s => G11 s * (etaS s : ℂ) - (eta1 s : ℂ) from funext id_G13]
    exact (cG11.mul (cr _ continuous_etaS)).sub (cr _ continuous_eta1)
  have cG20 : Continuous G20 := by
    have : G20 = fun s => ((-1 / κ 2 s : ℝ) : ℂ) := by funext s; simp [G20, kc]
    rw [this]; exact cr _ (continuous_const.div (continuous_κ 2) κ2_ne)
  have cG22 : Continuous G22 := by
    have : G22 = fun s => G20 s * (etaS s : ℂ) + G11 s ^ 2 - (L2 s : ℂ) := by
      funext s; have := id_G22 s; linear_combination this
    rw [this]
    exact ((cG20.mul (cr _ continuous_etaS)).add (cG11.pow 2)).sub (cr _ continuous_L2)
  have cG24 : Continuous G24 := by
    have : G24 = fun s => -(G22 s * (etaS s : ℂ)) + G20 s * G04 s + 2 * G11 s * G13 s +
        G20 s * (etaS s : ℂ) ^ 2 - 2 * (L2 s : ℂ) * (etaS s : ℂ) + (eta2 s : ℂ) := by
      funext s; have := id_G24 s; linear_combination this
    rw [this]
    have := cr _ continuous_etaS; have := cr _ continuous_L2; have := cr _ continuous_eta2
    have := continuous_G04
    fun_prop
  obtain ⟨k1, h1⟩ := exists_bound_on (σ := σ) cG02
  obtain ⟨k2, h2⟩ := exists_bound_on (σ := σ) continuous_G04
  obtain ⟨k3, h3⟩ := exists_bound_on (σ := σ) cG11
  obtain ⟨k4, h4⟩ := exists_bound_on (σ := σ) cG13
  obtain ⟨k5, h5⟩ := exists_bound_on (σ := σ) cG20
  obtain ⟨k6, h6⟩ := exists_bound_on (σ := σ) cG22
  obtain ⟨k7, h7⟩ := exists_bound_on (σ := σ) cG24
  obtain ⟨k8, h8⟩ := exists_bound_on (σ := σ) (cr _ continuous_L2)
  obtain ⟨k9, h9⟩ := exists_bound_on (σ := σ) (cr _ continuous_eta1)
  obtain ⟨k10, h10⟩ := exists_bound_on (σ := σ) (cr _ continuous_eta2)
  obtain ⟨k11, h11⟩ := exists_bound_on (σ := σ) (cr _ (continuous_κ 2))
  set K := 1 + max k1 0 + max k2 0 + max k3 0 + max k4 0 + max k5 0 + max k6 0 + max k7 0 +
    max k8 0 + max k9 0 + max k10 0 + max k11 0
  have l1 := le_max_left k1 0; have l2 := le_max_left k2 0; have l3 := le_max_left k3 0
  have l4 := le_max_left k4 0; have l5 := le_max_left k5 0; have l6 := le_max_left k6 0
  have l7 := le_max_left k7 0; have l8 := le_max_left k8 0; have l9 := le_max_left k9 0
  have l10 := le_max_left k10 0; have l11 := le_max_left k11 0
  have r1 := le_max_right k1 0; have r2 := le_max_right k2 0; have r3 := le_max_right k3 0
  have r4 := le_max_right k4 0; have r5 := le_max_right k5 0; have r6 := le_max_right k6 0
  have r7 := le_max_right k7 0; have r8 := le_max_right k8 0; have r9 := le_max_right k9 0
  have r10 := le_max_right k10 0; have r11 := le_max_right k11 0
  refine ⟨K, by simp only [K]; linarith, fun s hs => ?_⟩
  have g11 := h11 s hs
  rw [Complex.norm_real, Real.norm_eq_abs] at g11
  have := le_abs_self (κ 2 s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := h1 s hs; simp only [K]; linarith
  · have := h2 s hs; simp only [K]; linarith
  · have := h3 s hs; simp only [K]; linarith
  · have := h4 s hs; simp only [K]; linarith
  · have := h5 s hs; simp only [K]; linarith
  · have := h6 s hs; simp only [K]; linarith
  · have := h7 s hs; simp only [K]; linarith
  · have := h8 s hs; simp only [K]; linarith
  · have := h9 s hs; simp only [K]; linarith
  · have := h10 s hs; simp only [K]; linarith
  · simp only [K]; linarith

end EulerianBridge.Saddle
