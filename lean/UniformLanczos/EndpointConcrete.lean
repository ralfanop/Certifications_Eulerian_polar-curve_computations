/-
Uniform Lanczos note, Lemma 2 for the concrete limit `I'` (the inverse of `Λ'`).

* `Hint_unbounded` : `H(a) = (1/π) ∫₀^{π/2} a sin θ I'(a sin θ) dθ` is unbounded as `a ↑ 1/2`
  (for every `T` there is `a ∈ [1/4, 1/2)` with `H(a) ≥ T`), from `I'(y) ≥ 1/(1/2 - y) - 2`;
* `Ip_mem`, `Ip_G_continuousOn`: regularity of `y ↦ y I'(y)` on `[0,b]`, `b < 1/2`;
* `endpoint_concrete` : **Lemma 2(c) with every property of the limit proved**.  For
  `0 < t₁ ≤ t₂` there are `0 < lo < b < 1/2`, `K` and `M₀` such that for every `M ≥ M₀` and
  `t ∈ [t₁,t₂]` the limit root `a_t` and the finite-`M` root `a_{t,M}` exist in `(lo, b)`, the
  latter is unique in `[0,b]`, and `|a_{t,M} - a_t| ≤ K/M`.
The only hypotheses left concern the finite-`M` functions `P_M = φ_M'`: continuity, strict
monotonicity and `P_M(0) = 0` (log-concavity of B-splines, Floater 2024) and
`|φ_M' - I'| ≤ C_b/M` on `[0,b]` (Lemma 1).
-/
import UniformLanczos.Lambda
import UniformLanczos.Endpoint

open Set Real Filter Topology intervalIntegral

namespace UniformLanczos

lemma Ip_mem {y : ℝ} (h0 : 0 ≤ y) (h1 : y < 1 / 2) : y ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
  ⟨by linarith, h1⟩

lemma Ip_G_continuousOn {b : ℝ} (hb : b < 1 / 2) :
    ContinuousOn (fun y => y * Ip y) (Icc 0 b) := by
  apply continuousOn_id.mul
  exact Ip_continuousOn.mono fun y hy => Ip_mem hy.1 (lt_of_le_of_lt hy.2 hb)

theorem Hint_unbounded (T : ℝ) :
    ∃ a, 1 / 4 ≤ a ∧ a < 1 / 2 ∧ T ≤ Hint (fun y => y * Ip y) a := by
  set K := π * |T| + 1 with hK
  have hKpos : 1 ≤ K := by have := abs_nonneg T; have := pi_pos; nlinarith
  set δ := 1 / (4 * K) with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 4 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  set a := 1 / 2 - δ ^ 2 / 4 with ha
  have ha1 : 1 / 4 ≤ a := by nlinarith
  have ha2 : a < 1 / 2 := by have : 0 < δ ^ 2 := by positivity
                             linarith
  refine ⟨a, ha1, ha2, ?_⟩
  have hpi : δ < π / 2 := by linarith [two_le_pi]
  -- the integrand and its continuity
  set f : ℝ → ℝ := fun θ => a * sin θ * Ip (a * sin θ) with hf
  have hmem : ∀ θ ∈ Icc 0 (π / 2), a * sin θ ∈ Icc 0 a :=
    fun θ hθ => mul_sin_mem ⟨by linarith, le_rfl⟩ hθ
  have hfc : ContinuousOn f (Icc 0 (π / 2)) := by
    have hG := Ip_G_continuousOn ha2
    exact hG.comp (continuous_const.mul continuous_sin).continuousOn hmem
  have hint : ∀ c d, c ∈ Icc 0 (π / 2) → d ∈ Icc 0 (π / 2) → c ≤ d →
      IntervalIntegrable f MeasureTheory.volume c d := by
    intro c d hc hd hcd
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hcd]
    exact hfc.mono (Icc_subset_Icc hc.1 hd.2)
  have h0 : (0 : ℝ) ∈ Icc 0 (π / 2) := ⟨le_rfl, by linarith [pi_pos]⟩
  have hm : π / 2 - δ ∈ Icc 0 (π / 2) := ⟨by linarith, by linarith⟩
  have he : π / 2 ∈ Icc 0 (π / 2) := ⟨by linarith [pi_pos], le_rfl⟩
  have hsplit := integral_add_adjacent_intervals (hint 0 (π / 2 - δ) h0 hm (by linarith))
    (hint (π / 2 - δ) (π / 2) hm he (by linarith))
  -- first piece is nonnegative
  have hI1 : 0 ≤ ∫ θ in (0 : ℝ)..(π / 2 - δ), f θ := by
    apply integral_nonneg (by linarith)
    intro θ hθ
    have hy := hmem θ ⟨hθ.1, by linarith [hθ.2]⟩
    exact mul_nonneg hy.1 (Ip_nonneg hy.1 (lt_of_le_of_lt hy.2 ha2))
  -- second piece: f ≥ 1/(4δ²) - 1
  have hlow : ∀ θ ∈ Icc (π / 2 - δ) (π / 2), 1 / (4 * δ ^ 2) - 1 ≤ f θ := by
    intro θ hθ
    have hθ' : θ ∈ Icc 0 (π / 2) := ⟨by linarith [hθ.1], hθ.2⟩
    set y := a * sin θ with hy
    have hyI := hmem θ hθ'
    have hsin1 : sin θ ≤ 1 := sin_le_one θ
    have hsin : 1 - δ ^ 2 / 2 ≤ sin θ := by
      have h1 := one_sub_sq_div_two_le_cos (x := π / 2 - θ)
      rw [cos_pi_div_two_sub] at h1
      have h2 : (π / 2 - θ) ^ 2 ≤ δ ^ 2 := by
        apply pow_le_pow_left₀ (by linarith [hθ.2]) (by linarith [hθ.1])
      linarith
    have hδ2 : δ ^ 2 ≤ 1 / 16 := by nlinarith
    have hy8 : 1 / 8 ≤ y := by rw [hy]; nlinarith
    have hy2 : y ≤ 1 / 2 := by rw [hy]; nlinarith
    have hden : 1 / 2 - y ≤ δ ^ 2 / 2 := by rw [hy]; nlinarith
    have hdpos : 0 < 1 / 2 - y := by linarith [hyI.2]
    have hIp := Ip_lower hyI.1 (lt_of_le_of_lt hyI.2 ha2)
    have hq : 1 / (4 * δ ^ 2) ≤ y / (1 / 2 - y) := by
      rw [div_le_div_iff₀ (by positivity) hdpos]; nlinarith
    have hfy : f θ = y * Ip y := rfl
    have : y * (1 / (1 / 2 - y) - 2) = y / (1 / 2 - y) - 2 * y := by field_simp
    rw [hfy]
    calc 1 / (4 * δ ^ 2) - 1 ≤ y / (1 / 2 - y) - 2 * y := by linarith
      _ = y * (1 / (1 / 2 - y) - 2) := this.symm
      _ ≤ y * Ip y := mul_le_mul_of_nonneg_left hIp hyI.1
  have hI2 : δ * (1 / (4 * δ ^ 2) - 1) ≤ ∫ θ in (π / 2 - δ)..(π / 2), f θ := by
    have := integral_mono_on (by linarith : π / 2 - δ ≤ π / 2)
      (by simp : IntervalIntegrable (fun _ => 1 / (4 * δ ^ 2) - 1) MeasureTheory.volume
        (π / 2 - δ) (π / 2))
      (hint (π / 2 - δ) (π / 2) hm he (by linarith)) hlow
    simp only [integral_const, smul_eq_mul] at this
    linarith [show π / 2 - (π / 2 - δ) = δ by ring]
  have hval : δ * (1 / (4 * δ ^ 2) - 1) = K - δ := by
    rw [hδ]; field_simp; try ring
  have htotal : π * |T| ≤ ∫ θ in (0 : ℝ)..(π / 2), f θ := by
    rw [← hsplit]; nlinarith
  unfold Hint
  have hTabs : T ≤ |T| := le_abs_self T
  have hpos : 0 < π := pi_pos
  calc T ≤ |T| := hTabs
    _ = 1 / π * (π * |T|) := by field_simp
    _ ≤ 1 / π * ∫ θ in (0 : ℝ)..(π / 2), f θ := by gcongr

theorem endpoint_concrete (P : ℕ → ℝ → ℝ) {t₁ t₂ : ℝ} (ht₁ : 0 < t₁)
    (hP : ∀ b, 0 ≤ b → b < 1 / 2 → ∃ C, 0 ≤ C ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
      ContinuousOn (P M) (Icc 0 b) ∧ StrictMonoOn (P M) (Icc 0 b) ∧ P M 0 = 0 ∧
        ∀ y ∈ Icc 0 b, |P M y - Ip y| ≤ C / M) :
    ∃ b lo K : ℝ, ∃ M₀ : ℕ, 0 < lo ∧ lo < b ∧ b < 1 / 2 ∧ ∀ M : ℕ, M₀ ≤ M → ∀ t ∈ Icc t₁ t₂,
      (∃ a ∈ Ioo lo b, Hint (fun y => y * Ip y) a = t ∧
        ∀ a' ∈ Icc 0 b, Hint (fun y => y * Ip y) a' = t → a' = a) ∧
      (∃ aM ∈ Ioo lo b, Hint (fun y => y * P M y) aM = t ∧
        (∀ a' ∈ Icc 0 b, Hint (fun y => y * P M y) a' = t → a' = aM) ∧
        ∀ a ∈ Icc lo b, Hint (fun y => y * Ip y) a = t → |aM - a| ≤ K / M) := by
  -- choose b with H(b) ≥ t₂ + 1
  obtain ⟨b, hb1, hb2, hHb⟩ := Hint_unbounded (t₂ + 1)
  have hb0 : 0 ≤ b := by linarith
  set H := Hint (fun y => y * Ip y) with hHdef
  have hGc := Ip_G_continuousOn hb2
  have hHc : ContinuousOn H (Icc 0 b) := Hint_continuousOn hb0 hGc
  have hH0 : H 0 = 0 := Hint_zero (by simp)
  -- choose lo with H(lo) < t₁/2
  obtain ⟨ε, hε, hεH⟩ := Metric.continuousWithinAt_iff.mp (hHc 0 ⟨le_rfl, hb0⟩) (t₁ / 2)
    (by positivity)
  set lo := min (ε / 2) (b / 2) with hlo
  have hlo0 : 0 < lo := lt_min (by positivity) (by linarith)
  have hlob : lo < b := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hHlo : H lo < t₁ / 2 := by
    have hlI : lo ∈ Icc 0 b := ⟨hlo0.le, hlob.le⟩
    have hd : dist lo 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hlo0]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have := hεH hlI hd
    rw [hH0, Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  -- Lemma 1 data on [0,b]
  obtain ⟨C, hC, M₁, hM₁⟩ := hP b hb0 hb2
  set M₀ : ℕ := max M₁ (⌈b * C * (1 / t₁ + 1)⌉₊ + 1) with hM₀
  refine ⟨b, lo, 2 * b * C / (4 * lo), M₀, hlo0, hlob, hb2, ?_⟩
  intro M hM t htI
  obtain ⟨hPc, hPm, hP0, hPclose⟩ := hM₁ M (le_trans (le_max_left _ _) hM)
  have hMbig : b * C * (1 / t₁ + 1) < M := by
    have h1 : (⌈b * C * (1 / t₁ + 1)⌉₊ + 1 : ℕ) ≤ M := le_trans (le_max_right _ _) hM
    have h2 : b * C * (1 / t₁ + 1) ≤ ⌈b * C * (1 / t₁ + 1)⌉₊ := Nat.le_ceil _
    have h3 : ((⌈b * C * (1 / t₁ + 1)⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast h1
    push_cast at h3
    linarith
  have hMpos : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hMbig
  have hbC : 0 ≤ b * C := mul_nonneg hb0 hC
  have hsmall1 : b * C / (2 * M) < t₁ / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : b * C / t₁ < M := by
      have : b * C / t₁ ≤ b * C * (1 / t₁ + 1) := by
        rw [mul_add, mul_one, mul_one_div]; linarith
      linarith
    rw [div_lt_iff₀ ht₁] at this
    nlinarith
  have hsmall2 : b * C / (2 * M) < 1 := by
    rw [div_lt_one (by positivity)]
    have : b * C ≤ b * C * (1 / t₁ + 1) := by
      have : 0 ≤ b * C * (1 / t₁) := by positivity
      nlinarith
    linarith
  have hmarg₁ : H lo + b * C / (2 * M) < t₁ := by linarith
  have hmarg₂ : t₂ + b * C / (2 * M) < H b := by linarith
  have hIc : ContinuousOn Ip (Icc 0 b) :=
    Ip_continuousOn.mono fun y hy => Ip_mem hy.1 (lt_of_le_of_lt hy.2 hb2)
  have hInn : ∀ y ∈ Icc 0 b, 0 ≤ Ip y := fun y hy => Ip_nonneg hy.1 (lt_of_le_of_lt hy.2 hb2)
  have hIm : ∀ y y', 0 ≤ y → y ≤ y' → y' ≤ b → 4 * (y' - y) ≤ Ip y' - Ip y :=
    fun y y' h0 h h1 => Ip_slope h0 h (lt_of_le_of_lt h1 hb2)
  have hEL := endpoint_lemma (I1 := Ip) (P := P M) (b := b) (m := 4) (lo := lo) (hi := b)
    (C := C) (M := M) (t₁ := t₁) (t₂ := t₂) hb0 (by norm_num) hlo0 hlob le_rfl hC hMpos
    hIc Ip_zero hInn hIm hPc hPm hP0 hPclose hmarg₁ hmarg₂ t htI
  obtain ⟨⟨a, ha, hHa⟩, ⟨aM, haM, hHaM, huniq, hest⟩⟩ := hEL
  have hHm : StrictMonoOn H (Icc 0 b) :=
    Hint_strictMonoOn hb0 hGc (G_strictMono_of_Iprime
      (Ip_strictMonoOn.mono fun y hy => Ip_mem hy.1 (lt_of_le_of_lt hy.2 hb2)) Ip_zero)
  refine ⟨⟨a, ha, hHa, fun a' ha' h' => ?_⟩, ⟨aM, haM, hHaM, huniq, fun a'' ha'' h'' => ?_⟩⟩
  · exact hHm.injOn ha' ⟨hlo0.le.trans ha.1.le, ha.2.le⟩ (h'.trans hHa.symm)
  · have := hest a'' ha'' h''
    calc |aM - a''| ≤ 2 * b * C / (4 * lo * M) := this
      _ = 2 * b * C / (4 * lo) / M := by field_simp

end UniformLanczos
