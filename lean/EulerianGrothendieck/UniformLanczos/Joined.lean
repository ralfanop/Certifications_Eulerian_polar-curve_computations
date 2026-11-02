import UniformLanczos.EndpointConcrete
import Bridge.Saddle.Corollary
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Lemma 5.5 joined to the endpoint lemma (manuscript 12, Lemmas 5.5 and 5.7(b), Theorem 5.9)

The library `UniformLanczos` (Lemmas 5.3, 5.4, 5.7(b), 5.8, the scaling and uniformity steps of
Theorem 5.9, Corollary 5.10) took the conclusions of Lemma 5.5 on `[0,b]` as the hypothesis `hP` of
`endpoint_concrete`.  Lemma 5.5 is proved in `Bridge.Saddle` (`lemma_5_5`, `lemma_5_5_phi`).  Both
now compile with the same toolchain (Lean 4.24.0, Mathlib `f897ebcf`), and this module discharges
`hP` for the actual `φ_M = -(1/M) log g_M`:
* `|φ_M' - I'| ≤ C/M` on `[0,b]` (Lemma 5.5);
* `φ_M'' ≥ 1/v - C/M ≥ 4 - C/M > 0` (Lemma 5.5 and `v = Λ''(s) ≤ 1/4`), so `φ_M'` is strictly
  increasing on `[0,b]`;
* `φ_M'(0) = 0`, from the evenness of `w_M` (Fourier inversion and `A(-z) = A(z)`);
* `φ_M'` is continuous on `[0,b]`.
Hence `endpoint_actual`: Lemma 5.7(b) for the actual `φ_M`, with no hypothesis. -/

open Set Filter Topology MeasureTheory Complex

namespace UniformLanczos.Joined

open EulerianBridge.Saddle

theorem Lp_eq : UL.Lp = UniformLanczos.Lp := rfl

theorem Ip_eq : UL.Ip = UniformLanczos.Ip := rfl

theorem A_neg (z : ℂ) : A (-z) = A z := by
  by_cases hz : z = 0
  · subst hz; simp
  · rw [A_eq_closed (neg_ne_zero.mpr hz), A_eq_closed hz]
    field_simp
    ring_nf

/-- `w_M` is even. -/
theorem w_even (M : ℕ) (hM : 2 ≤ M) (y : ℝ) : w M (-y) = w M y := by
  have h1 := w_eq_Wint M hM 0 (-y)
  have h2 := w_eq_Wint M hM 0 y
  have hW : Wint M 0 0 (-y) = Wint M 0 0 y := by
    unfold Wint
    rw [show (∫ u : ℝ, Wf M 0 0 y u) = ∫ u : ℝ, Wf M 0 0 y (-u) from
      (integral_neg_eq_self (fun u => Wf M 0 0 y u) volume).symm]
    congr 1
    funext u
    unfold Wf
    have hA : A (((0:ℝ):ℂ) + ((-u:ℝ):ℂ) * I) = A (((0:ℝ):ℂ) + (u:ℂ) * I) := by
      rw [show ((0:ℝ):ℂ) + ((-u:ℝ):ℂ) * I = -(((0:ℝ):ℂ) + (u:ℂ) * I) by push_cast; ring, A_neg]
    rw [hA]
    congr 2
    push_cast
    ring
  have : ((w M (-y) : ℝ) : ℂ) = ((w M y : ℝ) : ℂ) := by rw [h1, h2, hW]
  exact_mod_cast this

theorem deriv_w_zero (M : ℕ) (hM : 3 ≤ M) : deriv (w M) 0 = 0 := by
  have heq : (fun y => w M (-y)) = w M := funext (fun y => w_even M (by omega) y)
  have h1 : deriv (fun y => w M (-y)) 0 = -deriv (w M) (-0) := deriv_comp_neg (w M) 0
  rw [heq, neg_zero] at h1
  linarith

theorem κ_two_le (s : ℝ) : κ 2 s ≤ 1 / 4 := by
  by_cases hs : s = 0
  · subst hs; rw [κ_two_zero]; norm_num
  · have h1 := hasDerivAt_κ 1 s
    rw [κ_one_eq_Lp] at h1
    have h2 := UL.hasDerivAt_Lp hs
    rw [h1.unique h2]
    rcases lt_or_gt_of_ne hs with h | h
    · rw [← Lpp_neg]; exact UL.Lpp_le_quarter (by linarith)
    · exact UL.Lpp_le_quarter h

/-- The hypothesis of `endpoint_concrete`, proved for `P M = φ_M'`. -/
theorem hP_actual : ∀ b, 0 ≤ b → b < 1 / 2 → ∃ C, 0 ≤ C ∧ ∃ M₁ : ℕ, ∀ M : ℕ, M₁ ≤ M →
    ContinuousOn (deriv (φM M)) (Icc 0 b) ∧ StrictMonoOn (deriv (φM M)) (Icc 0 b) ∧
      deriv (φM M) 0 = 0 ∧ ∀ y ∈ Icc 0 b, |deriv (φM M) y - UniformLanczos.Ip y| ≤ C / M := by
  intro b hb0 hb
  set b1 := (b + 1 / 2) / 2 with hb1def
  have hb1 : b < b1 := by rw [hb1def]; linarith
  have hb1' : b1 < 1 / 2 := by rw [hb1def]; linarith
  have hb10 : 0 < b1 := by linarith
  obtain ⟨M0, C, h55⟩ := lemma_5_5_phi hb10 hb1'
  obtain ⟨M0', C', hraw⟩ := lemma_5_5 hb10 hb1'
  set M₁ : ℕ := max (max M0 M0') (max 5 (⌈|C|⌉₊ + 1)) with hM₁
  refine ⟨|C|, abs_nonneg _, M₁, fun M hM => ?_⟩
  have hM0 : M0 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM0' : M0' ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hM5 : 5 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hMC : (⌈|C|⌉₊ + 1 : ℕ) ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hCM : |C| / M < 1 := by
    rw [div_lt_one hMpos]
    have h1 : |C| ≤ ⌈|C|⌉₊ := Nat.le_ceil _
    have h2 : ((⌈|C|⌉₊ + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hMC
    push_cast at h2
    linarith
  have hin : ∀ y ∈ Icc 0 b, y ∈ Icc (-b1) b1 := fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  -- the explicit form of φ_M' near each point of [-b1, b1]
  have hform : ∀ x ∈ Ioo (-b1) b1, deriv (φM M) =ᶠ[𝓝 x]
      fun y => -(deriv (w M) (M * y) / w M (M * y)) := by
    intro x hx
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hasDerivAt_φM (by omega) (hraw M hM0' y ⟨hy.1.le, hy.2.le⟩).1).deriv
  have hcont : ContinuousOn (deriv (φM M)) (Icc 0 b) := by
    intro x hx
    have hx1 : x ∈ Ioo (-b1) b1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hw := (hraw M hM0' x ⟨hx1.1.le, hx1.2.le⟩).1
    have hlin : Continuous fun y : ℝ => (M:ℝ) * y := continuous_const.mul continuous_id
    have cw : ContinuousAt (fun y => w M (M * y)) x :=
      ((w_continuous M (by omega)).comp hlin).continuousAt
    have cw1 : ContinuousAt (fun y => deriv (w M) (M * y)) x :=
      ((continuous_deriv_w (by omega)).comp hlin).continuousAt
    have hF : ContinuousAt (fun y => -(deriv (w M) (M * y) / w M (M * y))) x :=
      (cw1.div cw hw.ne').neg
    exact (hF.congr (hform x hx1).symm).continuousWithinAt
  refine ⟨hcont, ?_, ?_, ?_⟩
  · apply strictMonoOn_of_deriv_pos (convex_Icc 0 b) hcont
    intro x hx
    rw [interior_Icc] at hx
    have hx1 : x ∈ Icc (-b1) b1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    obtain ⟨-, h2, -⟩ := h55 M hM0 x hx1
    have hvpos : 0 < vx x := κ_two_pos _
    have hvle : vx x ≤ 1 / 4 := κ_two_le _
    have hinv : 4 ≤ (vx x)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hvpos]; linarith
    have hCM' : C / M ≤ |C| / M := div_le_div_of_nonneg_right (le_abs_self C) hMpos.le
    have := (abs_le.mp h2).1
    linarith
  · have hw0 := (hraw M hM0' 0 ⟨by linarith, by linarith⟩).1
    rw [(hasDerivAt_φM (by omega) hw0).deriv, mul_zero, deriv_w_zero M (by omega)]
    simp
  · intro y hy
    obtain ⟨h1, -, -⟩ := h55 M hM0 y (hin y hy)
    rw [← Ip_eq]
    exact h1.trans (div_le_div_of_nonneg_right (le_abs_self C) hMpos.le)

/-- **Lemma 5.7(b)** for the actual `φ_M`: no hypothesis remains. -/
theorem endpoint_actual {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) :
    ∃ b lo K : ℝ, ∃ M₀ : ℕ, 0 < lo ∧ lo < b ∧ b < 1 / 2 ∧ ∀ M : ℕ, M₀ ≤ M → ∀ t ∈ Icc t₁ t₂,
      (∃ a ∈ Ioo lo b, Hint (fun y => y * UniformLanczos.Ip y) a = t ∧
        ∀ a' ∈ Icc 0 b, Hint (fun y => y * UniformLanczos.Ip y) a' = t → a' = a) ∧
      (∃ aM ∈ Ioo lo b, Hint (fun y => y * deriv (φM M) y) aM = t ∧
        (∀ a' ∈ Icc 0 b, Hint (fun y => y * deriv (φM M) y) a' = t → a' = aM) ∧
        ∀ a ∈ Icc lo b, Hint (fun y => y * UniformLanczos.Ip y) a = t → |aM - a| ≤ K / M) :=
  endpoint_concrete (fun M => deriv (φM M)) ht₁ hP_actual

end UniformLanczos.Joined
