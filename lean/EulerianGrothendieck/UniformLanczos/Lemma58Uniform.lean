import UniformLanczos.Lemma58

/-!
# Manuscript 12, Lemma 5.8: conditions (i), (iii), (iv) and the uniform statement

Source: frozen `12.tex`, label `lem:ul-classQ`, eq. (ul-Lip), and Definition 1.1 of Levin and
Lubinsky, *Bounds and Asymptotics for Orthogonal Polynomials for Varying Weights* (2018), p. 6.

For the actual `φ_M` and `Q_{j,M}(y) = (M/(2j)) φ_M(a y) - log a/(2j)` on `(-1/(2a), 1/(2a))`:

* `tendsto_QjM_right`, `tendsto_QjM_left`: condition (i), `Q_{j,M}(y)/log(2+|y|) → +∞` at both
  endpoints of the interval, for every `M ≥ 2`, `j ≥ 1`, `a > 0`;
* `differentiableAt_deriv_φM`, `deriv_φM_lipschitz`: `φ_M'` is differentiable on `(-1/2, 1/2)`
  for `M ≥ 4`, hence Lipschitz on `[-c, c]` with any bound for `|φ_M''|` there;
* `lemma_5_8_uniform`: for `0 < t₁` there are `b < 1/2`, `r > 1` with `r b < 1/2`, a constant
  `L` and `M₀` such that for all `M ≥ M₀`, `j ≥ 1` with `t₁ ≤ j/M ≤ t₂` the root `a = ξ_{j,M}` of
  `Φ_M(a) = j/M` exists in `(lo, b)`, is unique in `[0, b]`, `[-r, r] ⊂ (-1/(2a), 1/(2a))`, and
  `Q_{j,M}'` is strictly increasing and continuous (ii), `L`-Lipschitz on `[-r, r]` (ul-Lip),
  Hölder there with exponents `1/4` (iii) and `3/4` (iv) and constants independent of `(j, M)`,
  and satisfies both Mhaskar–Rakhmanov–Saff equations (v).

The hypothesis `M ≥ M₀` is the manuscript's `j ≥ j₀`: `j/M ≤ t₂` and `j ≥ t₂ M₀` give `M ≥ M₀`.
The uniform bound for `φ_M''` is `Bridge.Saddle.lemma_5_5_phi` (Lemma 5.5); the location of the
root is `UniformLanczos.Joined.endpoint_actual` (Lemma 5.7(b)).
-/

open Set Filter Topology
open EulerianBridge.Saddle
open UniformLanczos.Lemma56

namespace UniformLanczos.Lemma58

/-! ### Condition (i) -/

theorem gM_continuous {M : ℕ} (hM : 2 ≤ M) : Continuous (gM M) := by
  show Continuous fun x : ℝ => (M:ℝ) * w M ((M:ℝ) * x)
  exact continuous_const.mul ((w_continuous M hM).comp (continuous_const.mul continuous_id))

/-- `g_M(1/2) = 0`, from the exact density on the last knot interval. -/
theorem gM_half {M : ℕ} (hM : 2 ≤ M) : gM M (1/2) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, M = n + 1 := ⟨M - 1, by omega⟩
  have hn : n ≠ 0 := by omega
  rw [gM_right_tail n (1/2) (by simp) (by simp)]
  simp [hn]

/-- `φ_M(x) → +∞` as `x → 1/2` from the left. -/
theorem tendsto_φM_half {M : ℕ} (hM : 2 ≤ M) : Tendsto (φM M) (𝓝[<] (1/2 : ℝ)) atTop := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h1 : Tendsto (gM M) (𝓝[<] (1/2 : ℝ)) (𝓝 0) := by
    have h : Tendsto (gM M) (𝓝 (1/2 : ℝ)) (𝓝 (gM M (1/2))) := (gM_continuous hM).tendsto _
    rw [gM_half hM] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 : ∀ᶠ x in 𝓝[<] (1/2 : ℝ), gM M x ∈ Ioi (0:ℝ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (-(1/2):ℝ) < 1/2 by norm_num)] with x hx
    show 0 < gM M x
    unfold gM
    exact mul_pos hMpos (w_scaled_pos hM hx)
  have h3 : Tendsto (gM M) (𝓝[<] (1/2 : ℝ)) (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨h1, h2⟩
  have h4 : Tendsto (fun x => Real.log (gM M x)) (𝓝[<] (1/2 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp h3
  have hneg : -(1 / (M:ℝ)) < 0 := by linarith [one_div_pos.mpr hMpos]
  have h5 : Tendsto (fun x => -(1 / (M:ℝ)) * Real.log (gM M x)) (𝓝[<] (1/2 : ℝ)) atTop :=
    h4.const_mul_atBot_of_neg hneg
  exact h5

theorem QjM_even {M : ℕ} (j : ℕ) (hM : 2 ≤ M) (a y : ℝ) : QjM M j a (-y) = QjM M j a y := by
  have h : a * -y = -(a * y) := by ring
  unfold QjM
  rw [h, φM_even hM]

/-- Condition (i) at the right endpoint: `Q_{j,M}(y)/log(2+|y|) → +∞` as `y → 1/(2a)` from the
left. -/
theorem tendsto_QjM_right {M j : ℕ} (hM : 2 ≤ M) (hj : 1 ≤ j) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y => QjM M j a y / Real.log (2 + |y|)) (𝓝[<] (1 / (2 * a))) atTop := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hane : a ≠ 0 := ha.ne'
  have e : a * (1 / (2 * a)) = 1 / 2 := by field_simp
  have hmul : Tendsto (fun y : ℝ => a * y) (𝓝[<] (1 / (2 * a))) (𝓝[<] (1/2 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun y : ℝ => a * y) (𝓝 (1 / (2 * a))) (𝓝 (a * (1 / (2 * a)))) :=
        (continuous_const.mul continuous_id).tendsto _
      rw [e] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      have hy' : y < 1 / (2 * a) := hy
      have h3 := mul_lt_mul_of_pos_left hy' ha
      show a * y < 1 / 2
      linarith
  have hφ : Tendsto (fun y : ℝ => φM M (a * y)) (𝓝[<] (1 / (2 * a))) atTop :=
    (tendsto_φM_half hM).comp hmul
  have hc : 0 < (M:ℝ) / (2 * (j:ℝ)) := div_pos hMpos (by linarith)
  have hQ : Tendsto (QjM M j a) (𝓝[<] (1 / (2 * a))) atTop := by
    have h1 : Tendsto (fun y : ℝ => (M:ℝ) / (2 * (j:ℝ)) * φM M (a * y))
        (𝓝[<] (1 / (2 * a))) atTop := hφ.const_mul_atTop hc
    have h2 := tendsto_atTop_add_const_right (𝓝[<] (1 / (2 * a)))
      (-(Real.log a / (2 * (j:ℝ)))) h1
    refine h2.congr (fun y => ?_)
    show (M:ℝ) / (2 * (j:ℝ)) * φM M (a * y) + -(Real.log a / (2 * (j:ℝ))) = QjM M j a y
    unfold QjM
    ring
  have hlt : (1:ℝ) < 2 + |1 / (2 * a)| := by linarith [abs_nonneg (1 / (2 * a))]
  have hlogpos : 0 < Real.log (2 + |1 / (2 * a)|) := Real.log_pos hlt
  have hne : (2:ℝ) + |1 / (2 * a)| ≠ 0 := by linarith
  have hg : Tendsto (fun y : ℝ => (Real.log (2 + |y|))⁻¹) (𝓝[<] (1 / (2 * a)))
      (𝓝 ((Real.log (2 + |1 / (2 * a)|))⁻¹)) := by
    have hc1 : ContinuousAt (fun y : ℝ => 2 + |y|) (1 / (2 * a)) :=
      (continuous_const.add continuous_abs).continuousAt
    have hc2 : ContinuousAt (fun y : ℝ => Real.log (2 + |y|)) (1 / (2 * a)) := hc1.log hne
    have hc3 : ContinuousAt (fun y : ℝ => (Real.log (2 + |y|))⁻¹) (1 / (2 * a)) :=
      hc2.inv₀ hlogpos.ne'
    exact hc3.tendsto.mono_left nhdsWithin_le_nhds
  have h := hQ.atTop_mul_pos (inv_pos.mpr hlogpos) hg
  refine h.congr (fun y => ?_)
  show QjM M j a y * (Real.log (2 + |y|))⁻¹ = QjM M j a y / Real.log (2 + |y|)
  rw [div_eq_mul_inv]

/-- Condition (i) at the left endpoint. -/
theorem tendsto_QjM_left {M j : ℕ} (hM : 2 ≤ M) (hj : 1 ≤ j) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y => QjM M j a y / Real.log (2 + |y|)) (𝓝[>] (-(1 / (2 * a)))) atTop := by
  have hneg : Tendsto (fun y : ℝ => -y) (𝓝[>] (-(1 / (2 * a)))) (𝓝[<] (1 / (2 * a))) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h : Tendsto (fun y : ℝ => -y) (𝓝 (-(1 / (2 * a)))) (𝓝 (-(-(1 / (2 * a))))) :=
        continuous_neg.tendsto _
      rw [neg_neg] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      have hy' : -(1 / (2 * a)) < y := hy
      show -y < 1 / (2 * a)
      linarith
  refine ((tendsto_QjM_right hM hj ha).comp hneg).congr (fun y => ?_)
  show QjM M j a (-y) / Real.log (2 + |-y|) = QjM M j a y / Real.log (2 + |y|)
  rw [QjM_even j hM, abs_neg]

/-! ### The Lipschitz bound (ul-Lip) -/

/-- `φ_M'` is differentiable on `(-1/2, 1/2)` for `M ≥ 4`. -/
theorem differentiableAt_deriv_φM {M : ℕ} (hM : 4 ≤ M) {x : ℝ}
    (hx : x ∈ Ioo (-(1/2):ℝ) (1/2)) : DifferentiableAt ℝ (deriv (φM M)) x := by
  have hM3 : 3 ≤ M := by omega
  have hM2 : 2 ≤ M := by omega
  have hform : deriv (φM M) =ᶠ[𝓝 x] fun y => -(deriv (w M) (M * y) / w M (M * y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hasDerivAt_φM_three hM3 (w_scaled_pos hM2 hy)).deriv
  have hlin : DifferentiableAt ℝ (fun y : ℝ => (M:ℝ) * y) x :=
    ((hasDerivAt_id x).const_mul (M:ℝ)).differentiableAt
  have d1 : DifferentiableAt ℝ (fun y : ℝ => deriv (w M) ((M:ℝ) * y)) x :=
    (hasDerivAt_deriv_w M hM 0 ((M:ℝ) * x)).differentiableAt.comp x hlin
  have d0 : DifferentiableAt ℝ (fun y : ℝ => w M ((M:ℝ) * y)) x :=
    (hasDerivAt_w M hM3 0 ((M:ℝ) * x)).differentiableAt.comp x hlin
  have hF : DifferentiableAt ℝ (fun y : ℝ => -(deriv (w M) ((M:ℝ) * y) / w M ((M:ℝ) * y))) x :=
    (d1.fun_div d0 (w_scaled_pos hM2 hx).ne').fun_neg
  exact hF.congr_of_eventuallyEq hform

/-- A bound for `|φ_M''|` on `[-c, c]`, `c < 1/2`, is a Lipschitz constant for `φ_M'` there. -/
theorem deriv_φM_lipschitz {M : ℕ} (hM : 4 ≤ M) {c C : ℝ} (hc : c < 1/2)
    (hbound : ∀ x ∈ Icc (-c) c, |deriv (deriv (φM M)) x| ≤ C) :
    ∀ u ∈ Icc (-c) c, ∀ v ∈ Icc (-c) c,
      |deriv (φM M) u - deriv (φM M) v| ≤ C * |u - v| := by
  intro u hu v hv
  have hd : ∀ x ∈ Icc (-c) c, DifferentiableAt ℝ (deriv (φM M)) x := fun x hx =>
    differentiableAt_deriv_φM hM ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hb : ∀ x ∈ Icc (-c) c, ‖deriv (deriv (φM M)) x‖ ≤ C := fun x hx => by
    rw [Real.norm_eq_abs]; exact hbound x hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc (-c) c) hv hu
  rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h

/-! ### The uniform statement -/

/-- **Lemma 5.8**, conditions (ii)–(v) with constants independent of `(j, M)`. -/
theorem lemma_5_8_uniform {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) :
    ∃ b lo r L : ℝ, ∃ M₀ : ℕ, 0 < lo ∧ lo < b ∧ b < 1/2 ∧ 1 < r ∧ r * b < 1/2 ∧ 0 ≤ L ∧
      ∀ M : ℕ, M₀ ≤ M → ∀ j : ℕ, 1 ≤ j → (j:ℝ) / M ∈ Icc t₁ t₂ →
        ∃ a ∈ Ioo lo b,
          Hint (fun y => y * deriv (φM M) y) a = (j:ℝ) / M ∧
          (∀ a' ∈ Icc 0 b, Hint (fun y => y * deriv (φM M) y) a' = (j:ℝ) / M → a' = a) ∧
          Icc (-r) r ⊆ Ioo (-(1 / (2 * a))) (1 / (2 * a)) ∧
          StrictMonoOn (QjM' M j a) (Ioo (-(1 / (2 * a))) (1 / (2 * a))) ∧
          ContinuousOn (QjM' M j a) (Ioo (-(1 / (2 * a))) (1 / (2 * a))) ∧
          (∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
            |QjM' M j a x - QjM' M j a y| ≤ L * |x - y|) ∧
          (∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
            |QjM' M j a x - QjM' M j a y| ≤ L * (2 * r) ^ (1 - (1/4:ℝ)) * |x - y| ^ (1/4:ℝ)) ∧
          (∀ x ∈ Icc (-r) r, ∀ y ∈ Icc (-r) r,
            |QjM' M j a x - QjM' M j a y| ≤ L * (2 * r) ^ (1 - (3/4:ℝ)) * |x - y| ^ (3/4:ℝ)) ∧
          (1 / Real.pi) * ∫ θ in (0:ℝ)..Real.pi, Real.cos θ * QjM' M j a (Real.cos θ) = 1 ∧
          ∫ θ in (0:ℝ)..Real.pi, QjM' M j a (Real.cos θ) = 0 := by
  obtain ⟨b, lo, K, M₀, hlo, hlob, hb, hend⟩ :=
    UniformLanczos.Joined.endpoint_actual (t₂ := t₂) ht₁
  have hb0 : 0 < b := by linarith
  have hbc : b < (1 + 2 * b) / 4 := by linarith
  have hc : (1 + 2 * b) / 4 < 1 / 2 := by linarith
  have hc0 : 0 < (1 + 2 * b) / 4 := by linarith
  obtain ⟨M0', C, h55⟩ := lemma_5_5_phi hc0 hc
  have hr1 : 1 < (1 + 2 * b) / 4 / b := (one_lt_div hb0).mpr hbc
  have hrb : (1 + 2 * b) / 4 / b * b = (1 + 2 * b) / 4 := div_mul_cancel₀ _ hb0.ne'
  have h2t : (0:ℝ) < 2 * t₁ := by linarith
  have hL0 : 0 ≤ b ^ 2 / (2 * t₁) * |C| :=
    mul_nonneg (div_nonneg (sq_nonneg b) h2t.le) (abs_nonneg C)
  refine ⟨b, lo, (1 + 2 * b) / 4 / b, b ^ 2 / (2 * t₁) * |C|, max M₀ (max M0' 4), hlo, hlob, hb,
    hr1, by rw [hrb]; exact hc, hL0, ?_⟩
  intro M hM j hj ht
  have hM₀ : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hM0' : M0' ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hM4 : 4 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hM3 : 3 ≤ M := by omega
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hjpos : (0:ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  obtain ⟨-, a, ha, hroot, huniq, -⟩ := hend M hM₀ _ ht
  have ha0 : 0 < a := lt_trans hlo ha.1
  have hr0 : 0 < (1 + 2 * b) / 4 / b := lt_trans one_pos hr1
  have har : a * ((1 + 2 * b) / 4 / b) ≤ (1 + 2 * b) / 4 := by
    calc a * ((1 + 2 * b) / 4 / b) ≤ b * ((1 + 2 * b) / 4 / b) :=
          mul_le_mul_of_nonneg_right ha.2.le hr0.le
      _ = (1 + 2 * b) / 4 := by rw [mul_comm]; exact hrb
  have hsub : Icc (-((1 + 2 * b) / 4 / b)) ((1 + 2 * b) / 4 / b) ⊆
      Ioo (-(1 / (2 * a))) (1 / (2 * a)) :=
    UniformLanczos.interval_contains ha0 (lt_of_le_of_lt har hc)
  have hφ : ∀ u ∈ Icc (-(a * ((1 + 2 * b) / 4 / b))) (a * ((1 + 2 * b) / 4 / b)),
      ∀ v ∈ Icc (-(a * ((1 + 2 * b) / 4 / b))) (a * ((1 + 2 * b) / 4 / b)),
      |deriv (φM M) u - deriv (φM M) v| ≤ |C| * |u - v| := by
    intro u hu v hv
    exact deriv_φM_lipschitz hM4 hc
      (fun x hx => ((h55 M hM0' x hx).2.2).trans (le_abs_self C))
      u ⟨by linarith [hu.1], by linarith [hu.2]⟩ v ⟨by linarith [hv.1], by linarith [hv.2]⟩
  have hLip0 := UniformLanczos.Qprime_lipschitz (φ1 := deriv (φM M)) (M := (M:ℝ)) (N := (j:ℝ))
    (r := (1 + 2 * b) / 4 / b) (Lφ := |C|) ha0 hMpos hjpos hφ
  have hcoef : a ^ 2 * (M:ℝ) / (2 * (j:ℝ)) * |C| ≤ b ^ 2 / (2 * t₁) * |C| := by
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg C)
    have h1 : a ^ 2 ≤ b ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ha.2.le) (by linarith : (0:ℝ) ≤ b + a)]
    have h3 : t₁ * (M:ℝ) ≤ (j:ℝ) := by
      have h := ht.1
      rwa [le_div_iff₀ hMpos] at h
    have h2 : (M:ℝ) / (2 * (j:ℝ)) ≤ 1 / (2 * t₁) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ) < 2 * (j:ℝ)) h2t]
      linarith
    calc a ^ 2 * (M:ℝ) / (2 * (j:ℝ)) = a ^ 2 * ((M:ℝ) / (2 * (j:ℝ))) := by ring
      _ ≤ b ^ 2 * (1 / (2 * t₁)) :=
          mul_le_mul h1 h2 (div_nonneg hMpos.le (by linarith)) (sq_nonneg b)
      _ = b ^ 2 / (2 * t₁) := by ring
  have hLip : ∀ x ∈ Icc (-((1 + 2 * b) / 4 / b)) ((1 + 2 * b) / 4 / b),
      ∀ y ∈ Icc (-((1 + 2 * b) / 4 / b)) ((1 + 2 * b) / 4 / b),
      |QjM' M j a x - QjM' M j a y| ≤ b ^ 2 / (2 * t₁) * |C| * |x - y| := by
    intro x hx y hy
    have h := hLip0 x hx y hy
    unfold QjM'
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _))
  refine ⟨a, ha, hroot, huniq, hsub, QjM'_strictMonoOn hM3 hj ha0, QjM'_continuousOn j hM3 ha0,
    hLip, UniformLanczos.holder_of_lipschitz hL0 (by norm_num) hLip,
    UniformLanczos.holder_of_lipschitz hL0 (by norm_num) hLip, ?_⟩
  exact mrs_actual hM3 hj ha0 ha.2.le hb hroot

/-- **Lemma 5.8**, condition (i) for the actual weights, at both endpoints. -/
theorem lemma_5_8_i {M j : ℕ} (hM : 2 ≤ M) (hj : 1 ≤ j) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y => QjM M j a y / Real.log (2 + |y|)) (𝓝[<] (1 / (2 * a))) atTop ∧
      Tendsto (fun y => QjM M j a y / Real.log (2 + |y|)) (𝓝[>] (-(1 / (2 * a)))) atTop :=
  ⟨tendsto_QjM_right hM hj ha, tendsto_QjM_left hM hj ha⟩

end UniformLanczos.Lemma58

#print axioms UniformLanczos.Lemma58.tendsto_QjM_right
#print axioms UniformLanczos.Lemma58.tendsto_QjM_left
#print axioms UniformLanczos.Lemma58.lemma_5_8_i
#print axioms UniformLanczos.Lemma58.differentiableAt_deriv_φM
#print axioms UniformLanczos.Lemma58.deriv_φM_lipschitz
#print axioms UniformLanczos.Lemma58.lemma_5_8_uniform
