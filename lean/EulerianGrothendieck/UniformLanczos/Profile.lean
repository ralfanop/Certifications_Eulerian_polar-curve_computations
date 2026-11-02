import UniformLanczos.EndpointConcrete
import UniformLanczos.HigherProfileCoefficients

/-! # Manuscript 12: Corollary 5.10 (the profile `F`) and Lemma 5.7(a)

`Φ(a) = (1/π)∫_0^{π/2} a sin θ I'(a sin θ) dθ` is `Hint (fun y => y * Ip y)`; `ξ_α` is the root of
`Φ(ξ) = α` and `F(α) = ξ_α²/4` (eq. (ul-F)).
* Corollary 5.10: `F` is continuous and strictly increasing on `(0,∞)`, `0 < F < 1/16`,
  `F(α) → 1/16` as `α → ∞`, and the seven-coefficient expansion with remainder `225 α^8`
  (`F_series`, from the certified `F_expansion7_explicit`).
* Lemma 5.7(a): for every `G` with the properties stated in Lemma 5.6 for `G(y) = y φ_M'(y)`
  (continuous on `[0,1/2)`, strictly increasing, `G(0) = 0`, `G(x) ≥ c/(1/2-x)` near `1/2`) the
  equation `Hint G ξ = t` has a unique root in `(0,1/2)` for every `t > 0`; for `G ≡ 0`
  (`M = 1`, `φ_1' ≡ 0`) it has none. -/

open Set Filter Topology Real

namespace UniformLanczos.Profile

open UniformLanczos

noncomputable def H : ℝ → ℝ := Hint (fun y => y * Ip y)

theorem H_cont {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) : ContinuousOn H (Icc 0 b) :=
  Hint_continuousOn hb0 (Ip_G_continuousOn hb)

theorem H_mono {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1 / 2) : StrictMonoOn H (Icc 0 b) :=
  Hint_strictMonoOn hb0 (Ip_G_continuousOn hb) (G_strictMono_of_Iprime
    (Ip_strictMonoOn.mono fun y hy => Ip_mem hy.1 (lt_of_le_of_lt hy.2 hb)) Ip_zero)

theorem H_zero : H 0 = 0 := Hint_zero (by simp)

theorem H_strictMonoOn : StrictMonoOn H (Ico 0 (1 / 2)) := by
  intro x hx y hy hxy
  exact H_mono hy.1 hy.2 ⟨hx.1, hxy.le⟩ ⟨hy.1, le_rfl⟩ hxy

theorem H_pos {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) : 0 < H a := by
  have := H_strictMonoOn ⟨le_rfl, by norm_num⟩ ⟨ha.le, ha2⟩ ha
  rwa [H_zero] at this

theorem exists_root {α : ℝ} (hα : 0 < α) : ∃ a ∈ Ioo 0 (1 / 2), H a = α := by
  obtain ⟨b, hb1, hb2, hHb⟩ := Hint_unbounded (α + 1)
  have hb0 : 0 ≤ b := by linarith
  obtain ⟨a, ha, hHa, -⟩ := exists_unique_root hb0 (H_cont hb0 hb2) (H_mono hb0 hb2)
    (by rw [H_zero]; exact hα) (by unfold H; linarith)
  exact ⟨a, ⟨ha.1, ha.2.trans hb2⟩, hHa⟩

/-- `ξ_α`, the root of `Φ(ξ) = α` (Lemma 5.4). -/
noncomputable def ξ (α : ℝ) : ℝ := if h : 0 < α then Classical.choose (exists_root h) else 0

theorem ξ_spec {α : ℝ} (hα : 0 < α) : ξ α ∈ Ioo 0 (1 / 2) ∧ H (ξ α) = α := by
  unfold ξ
  rw [dif_pos hα]
  exact Classical.choose_spec (exists_root hα)

theorem ξ_unique {α a : ℝ} (hα : 0 < α) (ha : a ∈ Ico 0 (1 / 2)) (h : H a = α) : a = ξ α :=
  H_strictMonoOn.injOn ha (Ioo_subset_Ico_self (ξ_spec hα).1) (h.trans (ξ_spec hα).2.symm)

theorem ξ_H {a : ℝ} (ha : a ∈ Ioo 0 (1 / 2)) : ξ (H a) = a :=
  (ξ_unique (H_pos ha.1 ha.2) (Ioo_subset_Ico_self ha) rfl).symm

theorem ξ_strictMonoOn : StrictMonoOn ξ (Ioi 0) := by
  intro α hα β hβ hαβ
  have sα := ξ_spec (show 0 < α from hα)
  have sβ := ξ_spec (show 0 < β from hβ)
  by_contra hle
  push_neg at hle
  have := H_strictMonoOn.monotoneOn (Ioo_subset_Ico_self sβ.1) (Ioo_subset_Ico_self sα.1) hle
  rw [sα.2, sβ.2] at this
  linarith

theorem ξ_image : ξ '' Ioi 0 = Ioo 0 (1 / 2) := by
  ext a
  constructor
  · rintro ⟨α, hα, rfl⟩; exact (ξ_spec hα).1
  · intro ha; exact ⟨H a, H_pos ha.1 ha.2, ξ_H ha⟩

theorem ξ_continuousOn : ContinuousOn ξ (Ioi 0) := by
  intro α hα
  apply ContinuousAt.continuousWithinAt
  apply ξ_strictMonoOn.continuousAt_of_image_mem_nhds (Ioi_mem_nhds hα)
  rw [ξ_image]
  exact Ioo_mem_nhds (ξ_spec hα).1.1 (ξ_spec hα).1.2

theorem ξ_tendsto : Tendsto ξ atTop (𝓝 (1 / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set a := max (1 / 4) (1 / 2 - ε / 2) with ha
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have ha2 : a < 1 / 2 := max_lt (by norm_num) (by linarith)
  refine ⟨H a + 1, fun α hα => ?_⟩
  have hα0 : 0 < α := by linarith [H_pos ha0 ha2]
  have s := ξ_spec hα0
  have hgt : a < ξ α := by
    by_contra hle
    push_neg at hle
    have := H_strictMonoOn.monotoneOn (Ioo_subset_Ico_self s.1) ⟨ha0.le, ha2⟩ hle
    rw [s.2] at this
    linarith
  rw [Real.dist_eq, abs_lt]
  constructor
  · have : 1 / 2 - ε / 2 ≤ a := le_max_right _ _
    linarith
  · linarith [s.1.2]

/-- The limit profile `F(α) = ξ_α²/4`, eq. (ul-F). -/
noncomputable def F (α : ℝ) : ℝ := ξ α ^ 2 / 4

theorem F_bounds {α : ℝ} (hα : 0 < α) : 0 < F α ∧ F α < 1 / 16 := by
  have s := (ξ_spec hα).1
  unfold F
  constructor
  · have := s.1; positivity
  · nlinarith [s.1, s.2]

theorem F_strictMonoOn : StrictMonoOn F (Ioi 0) := by
  intro α hα β hβ hαβ
  have h := ξ_strictMonoOn hα hβ hαβ
  have h0 := (ξ_spec (show 0 < α from hα)).1.1
  unfold F
  have : ξ α ^ 2 < ξ β ^ 2 := by nlinarith
  linarith

theorem F_continuousOn : ContinuousOn F (Ioi 0) :=
  (ξ_continuousOn.pow 2).div_const 4

theorem F_tendsto : Tendsto F atTop (𝓝 (1 / 16)) := by
  have h := (ξ_tendsto.pow 2).div_const 4
  convert h using 2
  norm_num

/-- `F(Φ(a)) = a²/4`. -/
theorem F_H {a : ℝ} (ha : a ∈ Ioo 0 (1 / 2)) : F (H a) = a ^ 2 / 4 := by
  unfold F; rw [ξ_H ha]

/-- Expansion (ul-Fseries) with the certified remainder: for `0 < α ≤ Φ(1/40)`,
`|F(α) - (α/12 - α²/20 + ⋯ - 1886176α⁷/2299171875)| ≤ 225 α⁸`. -/
theorem F_series {α : ℝ} (hα : 0 < α) (hα1 : α ≤ H (1 / 40)) :
    |F α - (α / 12 - α ^ 2 / 20 + 4 * α ^ 3 / 525 + 2 * α ^ 4 / 525 + 368 * α ^ 5 / 336875
      - 544 * α ^ 6 / 1340625 - 1886176 * α ^ 7 / 2299171875)| ≤ 225 * α ^ 8 := by
  have s := ξ_spec hα
  have hle : ξ α ≤ 1 / 40 := by
    by_contra hgt
    push_neg at hgt
    have := H_strictMonoOn ⟨by norm_num, by norm_num⟩ (Ioo_subset_Ico_self s.1) hgt
    rw [s.2] at this
    linarith
  have h := F_expansion7_explicit (ξ α) ⟨s.1.1.le, hle⟩
  unfold F
  have e : Hint (fun y => y * Ip y) (ξ α) = α := s.2
  rw [e] at h
  exact h

/-! ## Lemma 5.7(a) -/

theorem Ip_lt (y : ℝ) (hy0 : 0 < y) (hy : y < 1 / 2) : Ip y < 1 / (1 / 2 - y) := by
  have hs : 0 < Ip y := by
    have := Ip_strictMonoOn (Ip_mem le_rfl (by norm_num)) (Ip_mem hy0.le hy) hy0
    rwa [Ip_zero] at this
  have hL := half_sub_inv_lt_Lp hs
  rw [Lp_Ip (Ip_mem hy0.le hy)] at hL
  have hd : 0 < 1 / 2 - y := by linarith
  rw [lt_div_iff₀ hd]
  have : 1 / Ip y > 1 / 2 - y := by linarith
  rw [gt_iff_lt, lt_div_iff₀ hs] at this
  linarith

theorem integrable_comp {G : ℝ → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (hc : ContinuousOn G (Icc 0 a)) :
    IntervalIntegrable (fun θ => G (a * sin θ)) MeasureTheory.volume 0 (π / 2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [pi_pos])]
  exact hc.comp (continuous_const.mul continuous_sin).continuousOn
    (fun θ hθ => mul_sin_mem ⟨ha0, le_rfl⟩ hθ)

/-- Comparison: under the hypotheses of Lemma 5.6, `Hint G` is unbounded on `[0,1/2)`. -/
theorem Hint_G_unbounded (G : ℝ → ℝ) (hc : ∀ b, b < 1 / 2 → ContinuousOn G (Icc 0 b))
    (hm : StrictMonoOn G (Ico 0 (1 / 2))) (h0 : G 0 = 0) {c x0 : ℝ} (hc0 : 0 < c)
    (hx0 : 0 ≤ x0) (hx01 : x0 < 1 / 2) (hblow : ∀ x ∈ Ico x0 (1 / 2), c / (1 / 2 - x) ≤ G x)
    (T : ℝ) : ∃ a, 0 ≤ a ∧ a < 1 / 2 ∧ T ≤ Hint G a := by
  set K0 := 2 * c * (x0 * Ip x0) with hK0
  have hG0 : ∀ y ∈ Ico (0:ℝ) (1 / 2), 0 ≤ G y := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, h0]
    · rw [← h0]; exact (hm ⟨le_rfl, by norm_num⟩ hy h).le
  have hcomp : ∀ y ∈ Ico (0:ℝ) (1 / 2), 2 * c * (y * Ip y) - K0 ≤ G y := by
    intro y hy
    have hIp0 : 0 ≤ Ip y := Ip_nonneg hy.1 hy.2
    by_cases hyx : x0 ≤ y
    · have hy0 : 0 < y := by
        rcases eq_or_lt_of_le hy.1 with h | h
        · -- y = 0 forces x0 = 0; c/(1/2) ≤ G 0 = 0 is impossible
          exfalso
          have := hblow y ⟨hyx, hy.2⟩
          rw [← h, h0] at this
          have : 0 < c / (1 / 2 - 0) := by positivity
          linarith
        · exact h
      have hb := hblow y ⟨hyx, hy.2⟩
      have hlt := Ip_lt y hy0 hy.2
      have hK : 0 ≤ K0 := by
        rw [hK0]; have := Ip_nonneg hx0 hx01; positivity
      have h1 : c * Ip y ≤ c / (1 / 2 - y) := by
        rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hlt.le hc0.le
      have h2 : 2 * c * (y * Ip y) ≤ c * Ip y := by
        nlinarith [mul_nonneg (mul_nonneg hc0.le hIp0) (by linarith [hy.2] : (0:ℝ) ≤ 1 - 2 * y)]
      linarith
    · push_neg at hyx
      have hmono : y * Ip y ≤ x0 * Ip x0 :=
        mul_le_mul hyx.le (Ip_slope hy.1 hyx.le hx01 |> fun h => by linarith) hIp0 hx0
      have := hG0 y hy
      nlinarith [hc0]
  obtain ⟨a, ha1, ha2, hHa⟩ := Hint_unbounded ((T + K0 / 2) / (2 * c))
  refine ⟨a, by linarith, ha2, ?_⟩
  have ha0 : 0 ≤ a := by linarith
  have hcG := hc a ha2
  have hcI : ContinuousOn (fun y => 2 * c * (y * Ip y) - K0) (Icc 0 a) :=
    ((continuousOn_const.mul (Ip_G_continuousOn ha2)).sub continuousOn_const)
  have hint := intervalIntegral.integral_mono_on (by linarith [pi_pos] : (0:ℝ) ≤ π / 2)
    (integrable_comp ha0 hcI) (integrable_comp ha0 hcG)
    (fun θ hθ => hcomp _ ⟨(mul_sin_mem ⟨ha0, le_rfl⟩ hθ).1,
      lt_of_le_of_lt (mul_sin_mem ⟨ha0, le_rfl⟩ hθ).2 ha2⟩)
  have hsplit : ∫ θ in (0:ℝ)..(π / 2), (2 * c * (a * sin θ * Ip (a * sin θ)) - K0) =
      2 * c * (∫ θ in (0:ℝ)..(π / 2), a * sin θ * Ip (a * sin θ)) - K0 * (π / 2) := by
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    · simp; ring
    · exact (integrable_comp ha0 (Ip_G_continuousOn ha2)).const_mul _
    · exact intervalIntegrable_const
  rw [hsplit] at hint
  unfold Hint at hHa ⊢
  have hpi : 0 < π := pi_pos
  rw [div_le_iff₀ (by positivity)] at hHa
  have e1 : (1 / π) * (2 * c * (∫ θ in (0:ℝ)..(π / 2), a * sin θ * Ip (a * sin θ)) - K0 * (π / 2))
      ≤ (1 / π) * ∫ θ in (0:ℝ)..(π / 2), G (a * sin θ) :=
    mul_le_mul_of_nonneg_left hint (by positivity)
  have e2 : (1 / π) * (2 * c * (∫ θ in (0:ℝ)..(π / 2), a * sin θ * Ip (a * sin θ)) - K0 * (π / 2))
      = 2 * c * (1 / π * ∫ θ in (0:ℝ)..(π / 2), a * sin θ * Ip (a * sin θ)) - K0 / 2 := by
    field_simp
  linarith

/-- **Lemma 5.7(a)**, for `M ≥ 2`: under the conclusions of Lemma 5.6 for `G(y) = y φ_M'(y)`,
`Φ_M(ξ) = t` has a unique root in `(0,1/2)` for every `t > 0`. -/
theorem lemma_5_7a (G : ℝ → ℝ) (hc : ∀ b, b < 1 / 2 → ContinuousOn G (Icc 0 b))
    (hm : StrictMonoOn G (Ico 0 (1 / 2))) (h0 : G 0 = 0) {c x0 : ℝ} (hc0 : 0 < c)
    (hx0 : 0 ≤ x0) (hx01 : x0 < 1 / 2) (hblow : ∀ x ∈ Ico x0 (1 / 2), c / (1 / 2 - x) ≤ G x)
    {t : ℝ} (ht : 0 < t) :
    ∃ ξ ∈ Ioo 0 (1 / 2), Hint G ξ = t ∧ ∀ ξ' ∈ Ico 0 (1 / 2), Hint G ξ' = t → ξ' = ξ := by
  have hmI : ∀ b, 0 ≤ b → b < 1 / 2 → StrictMonoOn (Hint G) (Icc 0 b) := fun b hb0 hb =>
    Hint_strictMonoOn hb0 (hc b hb) (hm.mono fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hb⟩)
  have hmall : StrictMonoOn (Hint G) (Ico 0 (1 / 2)) := by
    intro x hx y hy hxy
    exact hmI y hy.1 hy.2 ⟨hx.1, hxy.le⟩ ⟨hy.1, le_rfl⟩ hxy
  obtain ⟨b, hb0, hb2, hHb⟩ := Hint_G_unbounded G hc hm h0 hc0 hx0 hx01 hblow (t + 1)
  obtain ⟨a, ha, hHa, -⟩ := exists_unique_root hb0 (Hint_continuousOn hb0 (hc b hb2))
    (hmI b hb0 hb2) (by rw [Hint_zero h0]; exact ht) (by linarith)
  refine ⟨a, ⟨ha.1, ha.2.trans hb2⟩, hHa, fun a' ha' h' => ?_⟩
  exact hmall.injOn ha' ⟨ha.1.le, ha.2.trans hb2⟩ (h'.trans hHa.symm)

/-- **Lemma 5.7(a)**, `M = 1`: `φ_1' ≡ 0`, so `Φ_1 ≡ 0` and `Φ_1(ξ) = t > 0` has no root. -/
theorem lemma_5_7a_one {t : ℝ} (ht : 0 < t) (ξ0 : ℝ) : Hint (fun y => y * (0:ℝ)) ξ0 ≠ t := by
  simp [Hint]
  exact ht.ne

end UniformLanczos.Profile
