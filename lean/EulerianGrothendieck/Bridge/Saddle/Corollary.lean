import Bridge.Saddle.Lemma55

/-!
# Lemma 5.5, final part: `C²` regularity and the consequences for `φ_M = -(1/M) log g_M`

* `lemma_5_5_C2`: for `M ≥ max M₀ 5` the second derivative of `E_M` is continuous on `[-b, b]`,
  so `E_M ∈ C²([-b,b])` and (68) is a bound for its `C²` norm;
* `lemma_5_5_phi`: `‖φ_M' - I'‖_{C¹([-b,b])} ≤ C/M` and `sup_{M ≥ M₀} sup_{|x| ≤ b} |φ_M''(x)| < ∞`
  (the "in particular" of Lemma 5.5), with `I' = s` and `I'' = 1/v`.
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-- `φ_M = -(1/M) log g_M`, eq. (53). -/
noncomputable def φM (M : ℕ) (x : ℝ) : ℝ := -(1 / (M:ℝ)) * Real.log (gM M x)

theorem continuous_deriv_w {M : ℕ} (hM : 4 ≤ M) : Continuous (deriv (w M)) := by
  rw [deriv_w_eq M (by omega) 0]
  have : Continuous (Wint M 1 0) := continuous_iff_continuousAt.mpr fun y =>
    (hasDerivAt_Wint M 1 (by omega) 0 y).continuousAt
  exact Complex.continuous_re.comp (continuous_const.mul this)

theorem continuous_deriv2_w {M : ℕ} (hM : 5 ≤ M) : Continuous (deriv (deriv (w M))) := by
  have heq : deriv (deriv (w M)) = fun y => ((2 * Real.pi : ℂ)⁻¹ * Wint M 2 0 y).re := by
    funext y; exact (hasDerivAt_deriv_w M (by omega) 0 y).deriv
  rw [heq]
  have : Continuous (Wint M 2 0) := continuous_iff_continuousAt.mpr fun y =>
    (hasDerivAt_Wint M 2 (by omega) 0 y).continuousAt
  exact Complex.continuous_re.comp (continuous_const.mul this)

theorem continuousAt_E2 {M : ℕ} (hM : 5 ≤ M) {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hw : 0 < w M (M * x)) : ContinuousAt (E2 M) x := by
  have hIp : ContinuousAt UL.Ip x := UL.Ip_continuousOn.continuousAt (Ioo_mem_nhds hx.1 hx.2)
  have hlin : Continuous fun y : ℝ => (M:ℝ) * y := continuous_const.mul continuous_id
  have cw : ContinuousAt (fun y => w M (M * y)) x :=
    ((w_continuous M (by omega)).comp hlin).continuousAt
  have cw1 : ContinuousAt (fun y => deriv (w M) (M * y)) x :=
    ((continuous_deriv_w (by omega)).comp hlin).continuousAt
  have cw2 : ContinuousAt (fun y => deriv (deriv (w M)) (M * y)) x :=
    ((continuous_deriv2_w hM).comp hlin).continuousAt
  have hk : ContinuousAt (fun y => κ 2 (UL.Ip y)) x := (continuous_κ 2).continuousAt.comp hIp
  have hL : ContinuousAt (fun y => L2 (UL.Ip y)) x := continuous_L2.continuousAt.comp hIp
  have he : ContinuousAt (fun y => eta2 (UL.Ip y)) x := continuous_eta2.continuousAt.comp hIp
  have hq1 := cw1.div cw hw.ne'
  have hq2 := cw2.div cw hw.ne'
  unfold E2
  exact ((((continuousAt_const.mul (hq2.sub (hq1.pow 2))).add
    (continuousAt_const.div hk (κ2_ne _))).add hL).sub (he.div_const _))

/-- `E_M ∈ C²([-b,b])`: the second derivative is continuous on `[-b,b]` for `M` large. -/
theorem lemma_5_5_C2 {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ∃ M0 : ℕ, ∀ M : ℕ, M0 ≤ M → ContinuousOn (deriv (deriv (EM M))) (Icc (-b) b) := by
  set b1 := (b + 1 / 2) / 2
  have hb1 : b < b1 := by simp only [b1]; linarith
  have hb1' : b1 < 1 / 2 := by simp only [b1]; linarith
  obtain ⟨M0, C, hM⟩ := lemma_5_5 (by linarith : 0 < b1) hb1'
  refine ⟨max M0 5, fun M hMM => ?_⟩
  have hM0 : M0 ≤ M := le_trans (le_max_left _ _) hMM
  have hM5 : 5 ≤ M := le_trans (le_max_right _ _) hMM
  have hcont : ContinuousOn (E2 M) (Icc (-b) b) := by
    intro x hx
    have hx1 : x ∈ Icc (-b1) b1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxI : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact (continuousAt_E2 hM5 hxI (hM M hM0 x hx1).1).continuousWithinAt
  refine hcont.congr (fun x hx => ?_)
  have hx1 : x ∈ Icc (-b1) b1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  exact (hM M hM0 x hx1).2.2.1.deriv

theorem hasDerivAt_φM {M : ℕ} (hM : 4 ≤ M) {x : ℝ} (hw : 0 < w M (M * x)) :
    HasDerivAt (φM M) (-(deriv (w M) (M * x) / w M (M * x))) x := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hg : gM M x ≠ 0 := by unfold gM; positivity
  have h := ((hasDerivAt_gM (by omega : 3 ≤ M) x).log hg).const_mul (-(1 / (M:ℝ)))
  unfold φM
  convert h using 1
  unfold gM
  field_simp

theorem bound3 {a l η M Ca K : ℝ} (hM : 1 ≤ M) (ha : |a| ≤ Ca) (hl : |l| ≤ K) (he : |η| ≤ K) :
    |-a / M + l / M - η / M ^ 2| ≤ (Ca + 2 * K) / M := by
  have hMpos : 0 < M := by linarith
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have t1 : |-a / M| ≤ Ca / M := by
    rw [abs_div, abs_neg, abs_of_pos hMpos]; exact div_le_div_of_nonneg_right ha hMpos.le
  have t2 : |l / M| ≤ K / M := by
    rw [abs_div, abs_of_pos hMpos]; exact div_le_div_of_nonneg_right hl hMpos.le
  have hK : 0 ≤ K := (abs_nonneg _).trans hl
  have t3 : |η / M ^ 2| ≤ K / M := by
    rw [abs_div, abs_of_pos (by positivity : 0 < M ^ 2)]
    calc |η| / M ^ 2 ≤ K / M ^ 2 := div_le_div_of_nonneg_right he (by positivity)
      _ ≤ K / M := div_le_div_of_nonneg_left hK hMpos hM2
  have h1 := abs_add_le (-a / M + l / M) (-(η / M ^ 2))
  have h2 := abs_add_le (-a / M) (l / M)
  rw [abs_neg, ← sub_eq_add_neg] at h1
  calc |-a / M + l / M - η / M ^ 2| ≤ Ca / M + K / M + K / M := by linarith
    _ = (Ca + 2 * K) / M := by ring

set_option maxHeartbeats 1000000 in
/-- The "in particular" of Lemma 5.5: `‖φ_M' - I'‖_{C¹([-b,b])} ≤ C/M`, `sup |φ_M''| < ∞`. -/
theorem lemma_5_5_phi {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ∃ M0 : ℕ, ∃ C : ℝ, ∀ M : ℕ, M0 ≤ M → ∀ x ∈ Icc (-b) b,
      |deriv (φM M) x - UL.Ip x| ≤ C / M ∧
      |deriv (deriv (φM M)) x - (vx x)⁻¹| ≤ C / M ∧
      |deriv (deriv (φM M)) x| ≤ C := by
  set b1 := (b + 1 / 2) / 2
  have hb1 : b < b1 := by simp only [b1]; linarith
  have hb1' : b1 < 1 / 2 := by simp only [b1]; linarith
  obtain ⟨M0, C, hM⟩ := lemma_5_5 (by linarith : 0 < b1) hb1'
  set σ := UL.Ip b1
  obtain ⟨K, hK1, hK⟩ := exists_coeff_bound σ
  obtain ⟨c0, hc0, hκ⟩ := exists_κ_two_lower σ
  set C' := |C| + 2 * K + c0⁻¹
  refine ⟨max M0 4, C', fun M hMM x hx => ?_⟩
  have hM0 : M0 ≤ M := le_trans (le_max_left _ _) hMM
  have hM4 : 4 ≤ M := le_trans (le_max_right _ _) hMM
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hx1 : x ∈ Icc (-b1) b1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨hw, hE1, hE2, -, hd1, hd2⟩ := hM M hM0 x hx1
  have hxI : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hs : |UL.Ip x| ≤ σ := abs_Ip_le hb1' (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  obtain ⟨-, -, b11, -, -, -, -, bL2, bη1, bη2, -⟩ := hK (UL.Ip x) hs
  have hL1 : |L1 (UL.Ip x)| ≤ K := by
    rw [id_G11, Complex.norm_real, Real.norm_eq_abs] at b11; exact b11
  rw [Complex.norm_real, Real.norm_eq_abs] at bL2 bη1 bη2
  -- |E1|, |E2| ≤ |C|
  have hsq : 1 ≤ (M:ℝ) * Real.sqrt M := by
    have : 1 ≤ Real.sqrt M := by rw [Real.one_le_sqrt]; exact hM1
    nlinarith
  have hCM : C / (M * Real.sqrt M) ≤ |C| := by
    calc C / (M * Real.sqrt M) ≤ |C| / (M * Real.sqrt M) := by gcongr; exact le_abs_self C
      _ ≤ |C| / 1 := by gcongr
      _ = |C| := div_one _
  have hE1v : deriv (EM M) x = E1 M x := hE1.deriv
  have hE2v : deriv (deriv (EM M)) x = E2 M x := hE2.deriv
  rw [hE1v] at hd1; rw [hE2v] at hd2
  have a1 : |E1 M x| ≤ |C| := hd1.trans hCM
  have a2 : |E2 M x| ≤ |C| := hd2.trans hCM
  -- first derivative of φ
  have hφ1 : deriv (φM M) x = -(deriv (w M) (M * x) / w M (M * x)) := (hasDerivAt_φM hM4 hw).deriv
  have hrel1 : deriv (φM M) x - UL.Ip x = -(E1 M x) / M + L1 (UL.Ip x) / M - eta1 (UL.Ip x) / (M:ℝ) ^ 2 := by
    rw [hφ1]; unfold E1; field_simp; ring
  -- second derivative of φ, via the neighbourhood where w > 0
  have hev : deriv (φM M) =ᶠ[𝓝 x] fun y => -(deriv (w M) (M * y) / w M (M * y)) := by
    have hopen : IsOpen (Ioo (-b1) b1) := isOpen_Ioo
    have hxo : x ∈ Ioo (-b1) b1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    filter_upwards [hopen.mem_nhds hxo] with y hy
    exact (hasDerivAt_φM hM4 (hM M hM0 y ⟨hy.1.le, hy.2.le⟩).1).deriv
  have hlin : HasDerivAt (fun y : ℝ => (M:ℝ) * y) M x := by
    simpa using (hasDerivAt_id x).const_mul (M:ℝ)
  have hw0 := hasDerivAt_w M (by omega) 0 (M * x)
  rw [← hw0.deriv] at hw0
  have hw1 := hasDerivAt_deriv_w M hM4 0 (M * x)
  rw [← hw1.deriv] at hw1
  have hq := ((hw1.comp x hlin).div (hw0.comp x hlin) hw.ne').neg
  have hφ2 : deriv (deriv (φM M)) x = -((deriv (deriv (w M)) (M * x) * M * w M (M * x) -
      deriv (w M) (M * x) * (deriv (w M) (M * x) * M)) / w M (M * x) ^ 2) := by
    rw [hev.deriv_eq]; exact hq.deriv
  have hrel2 : deriv (deriv (φM M)) x - (vx x)⁻¹ =
      -(E2 M x) / M + L2 (UL.Ip x) / M - eta2 (UL.Ip x) / (M:ℝ) ^ 2 := by
    rw [hφ2]; unfold E2 vx
    have hk := κ2_ne (UL.Ip x)
    field_simp; ring
  have hM2 : (1:ℝ) ≤ (M:ℝ) ^ 2 := by nlinarith
  have hb1 : |deriv (φM M) x - UL.Ip x| ≤ (|C| + 2 * K) / M := by
    rw [hrel1]; exact bound3 hM1 a1 hL1 bη1
  have hb2 : |deriv (deriv (φM M)) x - (vx x)⁻¹| ≤ (|C| + 2 * K) / M := by
    rw [hrel2]; exact bound3 hM1 a2 bL2 bη2
  have hK0 : 0 ≤ K := by linarith
  have hdiv : (|C| + 2 * K) / M ≤ C' := by
    calc (|C| + 2 * K) / M ≤ (|C| + 2 * K) / 1 := by gcongr
      _ ≤ C' := by simp only [C']; have := inv_nonneg.mpr hc0.le; linarith
  have hdivM : (|C| + 2 * K) / M ≤ C' / M := by
    gcongr; simp only [C']; have := inv_nonneg.mpr hc0.le; linarith
  refine ⟨hb1.trans hdivM, hb2.trans hdivM, ?_⟩
  have hv : (vx x)⁻¹ ≤ c0⁻¹ := by
    unfold vx; exact inv_anti₀ hc0 (hκ _ hs)
  have hv0 : 0 ≤ (vx x)⁻¹ := inv_nonneg.mpr (κ_two_pos _).le
  have := abs_sub_abs_le_abs_sub (deriv (deriv (φM M)) x) (vx x)⁻¹
  rw [abs_of_nonneg hv0] at this
  calc |deriv (deriv (φM M)) x| ≤ (|C| + 2 * K) / M + (vx x)⁻¹ := by linarith
    _ ≤ (|C| + 2 * K) / 1 + c0⁻¹ := by gcongr
    _ = C' := by simp only [C']; ring

end EulerianBridge.Saddle
