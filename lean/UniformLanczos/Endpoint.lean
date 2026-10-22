/-
Uniform Lanczos note, Lemma 2 (unique limiting and exact endpoints), formalised.

For `G : ℝ → ℝ` put `Hint G a = (1/π) ∫₀^{π/2} G(a sin θ) dθ`.  With `G(x) = x I'(x)` this is
the note's `H(a) = (1/π) ∫₀^a x I'(x)/√(a² - x²) dx` after `x = a sin θ`, and with
`G(x) = x φ_M'(x)` it is the left side of the finite-`M` endpoint equation.
(The substitution itself, an improper integral at `x = a`, is not formalised; the endpoint
equations are taken in the `θ`-form, which is the form used in the note's own proof.)

Proved here, with no `sorry`:
* `Hint_zero`, `Hint_strictMonoOn`, `Hint_continuousOn` : `H(0) = 0`, `H` strictly increasing and
  continuous on `[0,b]` whenever `G` is continuous and strictly increasing on `[0,b]` with `G 0 = 0`;
* `Hint_slope` : a quantitative lower bound `H(a') - H(a) ≥ κ lo (a' - a)/4` from
  `G(y') - G(y) ≥ κ y (y' - y)`;
* `G_slope_of_Iprime` : that hypothesis for `G(y) = y I'(y)` when `I' ≥ 0` and
  `I'(y') - I'(y) ≥ m (y' - y)` (i.e. `I'' ≥ m`, from `I'' = 1/v`);
* `G_strictMono_of_Iprime` : `G(y) = y P(y)` strictly increasing if `P` is, with `P 0 = 0`;
* `Hint_close` : `|G₁ - G₂| ≤ ε` on `[0,b]` ⇒ `|H₁ - H₂| ≤ ε/2` on `[0,b]`;
* `exists_unique_root` : existence and uniqueness of the root of `H = t`;
* `root_stability` : `|a_M - a_t| ≤ δ/c`;
* `endpoint_lemma` : the assembled Lemma 2: uniformly for `t ∈ [t₁,t₂]`, for every `M` with
  `C/M` below an explicit threshold, the finite-`M` root `a_M(t)` exists, is unique in `[0,b]`,
  lies in `[lo,hi]` and satisfies `|a_M(t) - a_t| ≤ 2 b C/(m lo M)`.
For the concrete `I'` all limit hypotheses are discharged in `EndpointConcrete.lean`
(`endpoint_concrete`).  Inputs that are hypotheses here (proved elsewhere or on paper): continuity and strict monotonicity of
`φ_M'` (Floater 2024 / log-concavity), the bound `|φ_M' - I'| ≤ C/M` on `[0,b]` (Lemma 1),
the properties `I' ≥ 0`, `I'' ≥ m > 0` on `[0,b]` (Legendre duality, `Cancellation.lean`),
and `H(lo) < t₁ ≤ t₂ < H(hi)` (which holds for suitable `lo, hi` because `H(0) = 0` and
`H(a) → ∞` as `a ↑ 1/2`).
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Order.IntermediateValue

open Set Real intervalIntegral

namespace UniformLanczos

/-- `Hint G a = (1/π) ∫₀^{π/2} G(a sin θ) dθ`. -/
noncomputable def Hint (G : ℝ → ℝ) (a : ℝ) : ℝ := (1 / π) * ∫ θ in (0 : ℝ)..(π / 2), G (a * sin θ)

lemma sin_mem_Icc {θ : ℝ} (hθ : θ ∈ Icc 0 (π / 2)) : sin θ ∈ Icc (0 : ℝ) 1 :=
  ⟨sin_nonneg_of_nonneg_of_le_pi hθ.1 (by linarith [hθ.2, pi_pos]), sin_le_one θ⟩

lemma mul_sin_mem {a b θ : ℝ} (ha : a ∈ Icc 0 b) (hθ : θ ∈ Icc 0 (π / 2)) :
    a * sin θ ∈ Icc 0 b := by
  have hs := sin_mem_Icc hθ
  exact ⟨mul_nonneg ha.1 hs.1, by nlinarith [ha.1, ha.2, hs.1, hs.2]⟩

/-- Clamp `G` to `[0,b]` to get a globally continuous function agreeing with `G` on `[0,b]`. -/
noncomputable def clamp (G : ℝ → ℝ) {b : ℝ} (hb : 0 ≤ b) : ℝ → ℝ :=
  fun y => G (projIcc 0 b hb y)

lemma clamp_continuous {G : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) (hG : ContinuousOn G (Icc 0 b)) :
    Continuous (clamp G hb) :=
  hG.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun y => (projIcc 0 b hb y).2)

lemma clamp_eq {G : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) {y : ℝ} (hy : y ∈ Icc 0 b) :
    clamp G hb y = G y := by
  simp [clamp, projIcc_of_mem hb hy]

lemma Hint_clamp {G : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) {a : ℝ} (ha : a ∈ Icc 0 b) :
    Hint (clamp G hb) a = Hint G a := by
  unfold Hint
  congr 1
  apply integral_congr
  intro θ hθ
  rw [uIcc_of_le (by linarith [pi_pos])] at hθ
  exact clamp_eq hb (mul_sin_mem ha hθ)

lemma integrable_comp {G : ℝ → ℝ} (hG : Continuous G) (a : ℝ) :
    IntervalIntegrable (fun θ => G (a * sin θ)) MeasureTheory.volume 0 (π / 2) :=
  (hG.comp (continuous_const.mul continuous_sin)).intervalIntegrable _ _

theorem Hint_zero {G : ℝ → ℝ} (h0 : G 0 = 0) : Hint G 0 = 0 := by
  simp [Hint, h0]

theorem Hint_continuousOn {G : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) (hG : ContinuousOn G (Icc 0 b)) :
    ContinuousOn (Hint G) (Icc 0 b) := by
  have hc : Continuous (Hint (clamp G hb)) := by
    unfold Hint
    refine continuous_const.mul ?_
    have hcu : Continuous (Function.uncurry fun (a θ : ℝ) => clamp G hb (a * sin θ)) :=
      (clamp_continuous hb hG).comp (continuous_fst.mul (continuous_sin.comp continuous_snd))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hcu 0 (π / 2)
  refine (hc.continuousOn).congr ?_
  intro a ha
  exact (Hint_clamp hb ha).symm

theorem Hint_strictMonoOn {G : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b) (hG : ContinuousOn G (Icc 0 b))
    (hmono : StrictMonoOn G (Icc 0 b)) : StrictMonoOn (Hint G) (Icc 0 b) := by
  intro a ha a' ha' haa'
  rw [← Hint_clamp hb ha, ← Hint_clamp hb ha']
  unfold Hint
  have hpi : (0 : ℝ) < π / 2 := by linarith [pi_pos]
  refine mul_lt_mul_of_pos_left ?_ (by positivity)
  have hcG := clamp_continuous hb hG
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt hpi
    ((hcG.comp (continuous_const.mul continuous_sin)).continuousOn)
    ((hcG.comp (continuous_const.mul continuous_sin)).continuousOn) ?_ ?_
  · intro θ hθ
    have hθ' : θ ∈ Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2⟩
    rw [clamp_eq hb (mul_sin_mem ha hθ'), clamp_eq hb (mul_sin_mem ha' hθ')]
    have hs := sin_mem_Icc hθ'
    exact hmono.monotoneOn (mul_sin_mem ha hθ') (mul_sin_mem ha' hθ')
      (mul_le_mul_of_nonneg_right haa'.le hs.1)
  · refine ⟨π / 2, ⟨hpi.le, le_rfl⟩, ?_⟩
    have hθ' : π / 2 ∈ Icc 0 (π / 2) := ⟨hpi.le, le_rfl⟩
    rw [clamp_eq hb (mul_sin_mem ha hθ'), clamp_eq hb (mul_sin_mem ha' hθ')]
    simp only [sin_pi_div_two, mul_one]
    exact hmono ha ha' haa'

theorem Hint_close {G₁ G₂ : ℝ → ℝ} {b ε : ℝ} (hb : 0 ≤ b)
    (h₁ : ContinuousOn G₁ (Icc 0 b)) (h₂ : ContinuousOn G₂ (Icc 0 b))
    (hε : ∀ y ∈ Icc 0 b, |G₁ y - G₂ y| ≤ ε) :
    ∀ a ∈ Icc 0 b, |Hint G₁ a - Hint G₂ a| ≤ ε / 2 := by
  intro a ha
  rw [← Hint_clamp hb ha, ← Hint_clamp (G := G₂) hb ha]
  unfold Hint
  have hpi : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  rw [← mul_sub, ← integral_sub (integrable_comp (clamp_continuous hb h₁) a)
    (integrable_comp (clamp_continuous hb h₂) a), abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  have hbound : ‖∫ θ in (0 : ℝ)..(π / 2),
      (clamp G₁ hb (a * sin θ) - clamp G₂ hb (a * sin θ))‖ ≤ ε * |π / 2 - 0| := by
    apply norm_integral_le_of_norm_le_const
    intro θ hθ
    rw [uIoc_of_le hpi] at hθ
    have hθ' : θ ∈ Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2⟩
    rw [clamp_eq hb (mul_sin_mem ha hθ'), clamp_eq hb (mul_sin_mem ha hθ'), Real.norm_eq_abs]
    exact hε _ (mul_sin_mem ha hθ')
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hpi] at hbound
  calc 1 / π * |∫ θ in (0 : ℝ)..(π / 2), (clamp G₁ hb (a * sin θ) - clamp G₂ hb (a * sin θ))|
      ≤ 1 / π * (ε * (π / 2)) := by gcongr
    _ = ε / 2 := by field_simp

/-- `∫₀^{π/2} sin² = π/4`. -/
lemma integral_sin_sq_half_pi : ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ 2 = π / 4 := by
  rw [integral_sin_sq]
  simp [sin_pi_div_two, cos_pi_div_two]
  ring

theorem Hint_slope {G : ℝ → ℝ} {b κ lo : ℝ} (hb : 0 ≤ b) (hG : ContinuousOn G (Icc 0 b))
    (hκ : 0 ≤ κ) (hlo : 0 ≤ lo)
    (hslope : ∀ y y', 0 ≤ y → y ≤ y' → y' ≤ b → κ * y * (y' - y) ≤ G y' - G y) :
    ∀ a a', lo ≤ a → a ≤ a' → a' ≤ b → κ * lo / 4 * (a' - a) ≤ Hint G a' - Hint G a := by
  intro a a' hloa haa' ha'b
  have ha : a ∈ Icc 0 b := ⟨hlo.trans hloa, haa'.trans ha'b⟩
  have ha' : a' ∈ Icc 0 b := ⟨ha.1.trans haa', ha'b⟩
  rw [← Hint_clamp hb ha, ← Hint_clamp hb ha']
  unfold Hint
  have hpi : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  have hcG := clamp_continuous hb hG
  rw [← mul_sub, ← integral_sub (integrable_comp hcG a') (integrable_comp hcG a)]
  have hlow : ∫ θ in (0 : ℝ)..(π / 2), κ * lo * (a' - a) * sin θ ^ 2 ≤
      ∫ θ in (0 : ℝ)..(π / 2), (clamp G hb (a' * sin θ) - clamp G hb (a * sin θ)) := by
    apply integral_mono_on hpi
    · exact (continuous_const.mul ((continuous_sin).pow 2)).intervalIntegrable _ _
    · exact (integrable_comp hcG a').sub (integrable_comp hcG a)
    intro θ hθ
    rw [clamp_eq hb (mul_sin_mem ha' hθ), clamp_eq hb (mul_sin_mem ha hθ)]
    have hs := sin_mem_Icc hθ
    have h1 := hslope (a * sin θ) (a' * sin θ) (mul_nonneg ha.1 hs.1)
      (mul_le_mul_of_nonneg_right haa' hs.1) (mul_sin_mem ha' hθ).2
    have h2 : κ * lo * (a' - a) * sin θ ^ 2 ≤ κ * (a * sin θ) * (a' * sin θ - a * sin θ) := by
      have : κ * (a * sin θ) * (a' * sin θ - a * sin θ) = κ * a * (a' - a) * sin θ ^ 2 := by ring
      rw [this]
      have hd : 0 ≤ (a' - a) * sin θ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
      have : κ * lo ≤ κ * a := mul_le_mul_of_nonneg_left hloa hκ
      nlinarith
    linarith
  rw [intervalIntegral.integral_const_mul, integral_sin_sq_half_pi] at hlow
  have hpos : (0 : ℝ) < 1 / π := by positivity
  calc κ * lo / 4 * (a' - a) = 1 / π * (κ * lo * (a' - a) * (π / 4)) := by
        field_simp
    _ ≤ 1 / π * ∫ θ in (0 : ℝ)..(π / 2), (clamp G hb (a' * sin θ) - clamp G hb (a * sin θ)) :=
        mul_le_mul_of_nonneg_left hlow hpos.le

theorem G_slope_of_Iprime {P : ℝ → ℝ} {b m : ℝ}
    (hnn : ∀ y ∈ Icc 0 b, 0 ≤ P y)
    (hm : ∀ y y', 0 ≤ y → y ≤ y' → y' ≤ b → m * (y' - y) ≤ P y' - P y) :
    ∀ y y', 0 ≤ y → y ≤ y' → y' ≤ b → m * y * (y' - y) ≤ y' * P y' - y * P y := by
  intro y y' hy hyy' hy'b
  have h1 := hm y y' hy hyy' hy'b
  have h2 := hnn y' ⟨hy.trans hyy', hy'b⟩
  have : y' * P y' - y * P y = (y' - y) * P y' + y * (P y' - P y) := by ring
  rw [this]
  have : m * y * (y' - y) = y * (m * (y' - y)) := by ring
  rw [this]
  nlinarith [mul_nonneg (sub_nonneg.mpr hyy') h2, mul_le_mul_of_nonneg_left h1 hy]

theorem G_strictMono_of_Iprime {P : ℝ → ℝ} {b : ℝ} (hP : StrictMonoOn P (Icc 0 b))
    (hP0 : P 0 = 0) : StrictMonoOn (fun y => y * P y) (Icc 0 b) := by
  intro y hy y' hy' hlt
  have hb : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hy.1.trans hy.2⟩
  have hPy' : 0 < P y' := by
    rw [← hP0]; exact hP hb hy' (lt_of_le_of_lt hy.1 hlt)
  have hPy : 0 ≤ P y := by
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h, hP0]
    · rw [← hP0]; exact (hP hb hy h).le
  have hPP : P y < P y' := hP hy hy' hlt
  show y * P y < y' * P y'
  rcases eq_or_lt_of_le hy.1 with h | h
  · rw [← h]; simp; exact mul_pos (lt_of_le_of_lt hy.1 hlt) hPy'
  · nlinarith

theorem exists_unique_root {H : ℝ → ℝ} {b t : ℝ} (hb : 0 ≤ b) (hc : ContinuousOn H (Icc 0 b))
    (hm : StrictMonoOn H (Icc 0 b)) (ht0 : H 0 < t) (htb : t < H b) :
    ∃ a ∈ Ioo 0 b, H a = t ∧ ∀ a' ∈ Icc 0 b, H a' = t → a' = a := by
  obtain ⟨a, ha, hHa⟩ := intermediate_value_Ioo hb hc ⟨ht0, htb⟩
  refine ⟨a, ha, hHa, fun a' ha' hHa' => ?_⟩
  exact hm.injOn ha' (Ioo_subset_Icc_self ha) (hHa'.trans hHa.symm)

theorem root_stability {H HM : ℝ → ℝ} {lo hi c δ t aM a : ℝ} (hc : 0 < c)
    (hslope : ∀ x y, lo ≤ x → x ≤ y → y ≤ hi → c * (y - x) ≤ H y - H x)
    (hclose : ∀ x ∈ Icc lo hi, |HM x - H x| ≤ δ)
    (haM : aM ∈ Icc lo hi) (ha : a ∈ Icc lo hi) (hHM : HM aM = t) (hH : H a = t) :
    |aM - a| ≤ δ / c := by
  have hd : |H aM - H a| ≤ δ := by
    have := hclose aM haM
    rw [hHM] at this; rw [hH, abs_sub_comm]; exact this
  rw [le_div_iff₀ hc]
  rcases le_total aM a with h | h
  · have := hslope aM a haM.1 h ha.2
    rw [abs_of_nonpos (by linarith)]
    have : H a - H aM ≤ δ := by rw [abs_le] at hd; linarith [hd.1]
    nlinarith
  · have := hslope a aM ha.1 h haM.2
    rw [abs_of_nonneg (by linarith)]
    have : H aM - H a ≤ δ := by rw [abs_le] at hd; linarith [hd.2]
    nlinarith

/-- **Lemma 2, assembled.**  `I1 = I'` (limit) and `P = φ_M'` (finite `M`) on `[0,b]`.
Hypothesis `hPclose` is the conclusion `‖φ_M' - I'‖ ≤ C/M` of Lemma 1. -/
theorem endpoint_lemma {I1 P : ℝ → ℝ} {b m lo hi C M t₁ t₂ : ℝ}
    (hb : 0 ≤ b) (hm : 0 < m) (hlo : 0 < lo) (hlohi : lo < hi) (hhib : hi ≤ b)
    (hC : 0 ≤ C) (hM : 0 < M)
    -- limit data
    (hIc : ContinuousOn I1 (Icc 0 b)) (hI0 : I1 0 = 0) (hInn : ∀ y ∈ Icc 0 b, 0 ≤ I1 y)
    (hIm : ∀ y y', 0 ≤ y → y ≤ y' → y' ≤ b → m * (y' - y) ≤ I1 y' - I1 y)
    -- finite-M data (Floater / log-concavity, and Lemma 1)
    (hPc : ContinuousOn P (Icc 0 b)) (hPm : StrictMonoOn P (Icc 0 b)) (hP0 : P 0 = 0)
    (hPclose : ∀ y ∈ Icc 0 b, |P y - I1 y| ≤ C / M)
    -- the compact ratio interval sits strictly inside H([lo,hi]) with margin
    (hmarg₁ : Hint (fun y => y * I1 y) lo + b * C / (2 * M) < t₁)
    (hmarg₂ : t₂ + b * C / (2 * M) < Hint (fun y => y * I1 y) hi) :
    ∀ t ∈ Icc t₁ t₂,
      (∃ a ∈ Ioo lo hi, Hint (fun y => y * I1 y) a = t) ∧
      (∃ aM ∈ Ioo lo hi, Hint (fun y => y * P y) aM = t ∧
        (∀ a' ∈ Icc 0 b, Hint (fun y => y * P y) a' = t → a' = aM) ∧
        ∀ a ∈ Icc lo hi, Hint (fun y => y * I1 y) a = t →
          |aM - a| ≤ 2 * b * C / (m * lo * M)) := by
  intro t ht'
  set H := Hint (fun y => y * I1 y)
  set HM := Hint (fun y => y * P y)
  have hlo0 : (0 : ℝ) ≤ lo := hlo.le
  have hGc : ContinuousOn (fun y => y * I1 y) (Icc 0 b) := continuousOn_id.mul hIc
  have hGPc : ContinuousOn (fun y => y * P y) (Icc 0 b) := continuousOn_id.mul hPc
  have hδ : 0 ≤ b * C / (2 * M) := by positivity
  -- |y P - y I1| ≤ b C/M on [0,b]
  have hGclose : ∀ y ∈ Icc 0 b, |y * P y - y * I1 y| ≤ b * C / M := by
    intro y hy
    rw [← mul_sub, abs_mul, abs_of_nonneg hy.1]
    calc y * |P y - I1 y| ≤ b * (C / M) :=
          mul_le_mul hy.2 (hPclose y hy) (abs_nonneg _) hb
      _ = b * C / M := by ring
  have hHclose : ∀ a ∈ Icc 0 b, |HM a - H a| ≤ b * C / (2 * M) := by
    intro a ha
    have := Hint_close hb hGPc hGc hGclose a ha
    calc |HM a - H a| ≤ b * C / M / 2 := this
      _ = b * C / (2 * M) := by ring
  have hHc : ContinuousOn H (Icc 0 b) := Hint_continuousOn hb hGc
  have hHMc : ContinuousOn HM (Icc 0 b) := Hint_continuousOn hb hGPc
  have hImono : StrictMonoOn I1 (Icc 0 b) := by
    intro y hy y' hy' hlt
    have := hIm y y' hy.1 hlt.le hy'.2
    nlinarith
  have hHm : StrictMonoOn H (Icc 0 b) := Hint_strictMonoOn hb hGc (G_strictMono_of_Iprime hImono hI0)
  have hHMm : StrictMonoOn HM (Icc 0 b) := Hint_strictMonoOn hb hGPc (G_strictMono_of_Iprime hPm hP0)
  have hloI : lo ∈ Icc 0 b := ⟨hlo0, hlohi.le.trans hhib⟩
  have hhiI : hi ∈ Icc 0 b := ⟨hlo0.trans hlohi.le, hhib⟩
  have hsub : Icc lo hi ⊆ Icc 0 b := Icc_subset_Icc hlo0 hhib
  -- limit root in (lo,hi)
  have hlim : ∃ a ∈ Ioo lo hi, H a = t := by
    have hc' : ContinuousOn H (Icc lo hi) := hHc.mono hsub
    have hmem : t ∈ Ioo (H lo) (H hi) := ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    obtain ⟨a, ha, h⟩ := intermediate_value_Ioo hlohi.le hc' hmem
    exact ⟨a, ha, h⟩
  refine ⟨hlim, ?_⟩
  -- finite-M root in (lo,hi)
  have hMlo : HM lo < t := by
    have := hHclose lo hloI; rw [abs_le] at this; linarith [ht'.1, this.2]
  have hMhi : t < HM hi := by
    have := hHclose hi hhiI; rw [abs_le] at this; linarith [ht'.2, this.1]
  obtain ⟨aM, haM, hHMa⟩ := intermediate_value_Ioo hlohi.le (hHMc.mono hsub) ⟨hMlo, hMhi⟩
  refine ⟨aM, haM, hHMa, ?_, ?_⟩
  · intro a' ha' h'
    exact hHMm.injOn ha' (hsub (Ioo_subset_Icc_self haM)) (h'.trans hHMa.symm)
  · intro a ha hHa
    have hslopeG := G_slope_of_Iprime (P := I1) hInn hIm
    have hsl := Hint_slope hb hGc hm.le hlo0 hslopeG
    have hc : 0 < m * lo / 4 := by positivity
    have hst := root_stability (H := H) (HM := HM) (lo := lo) (hi := hi) hc
      (fun x y hx hxy hy => hsl x y hx hxy (hy.trans hhib))
      (fun x hx => hHclose x (hsub hx)) (Ioo_subset_Icc_self haM) ha hHMa hHa
    calc |aM - a| ≤ b * C / (2 * M) / (m * lo / 4) := hst
      _ = 2 * b * C / (m * lo * M) := by field_simp; ring

end UniformLanczos
