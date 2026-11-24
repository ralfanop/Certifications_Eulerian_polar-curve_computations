import UniformLanczos.Lemma513ActualGM
import Mathlib

/-! M12 Lemma 5.13, current TeX label lem:ul-rate-localisation.
Endpoint closure on the actual scaled cardinal B-spline, not continuity of log g.
The logarithmic derivative times g extends via |g'|/M to the full real line.
Uniform constants are selected from a fixed enlarged proportional interval;
the previously proved first-tail estimate and classical Legendre inequalities
are explicit inputs to the final assembly.
-/
namespace UniformLanczos.Lemma513SupportUniform
open Set MeasureTheory Filter intervalIntegral
open EulerianBridge.Saddle UniformLanczos.Lemma56 UniformLanczos.Lemma513ActualGM

theorem actual_gM_zero_outside {M : ℕ} (hM : 3 ≤ M) {x : ℝ}
    (hx : (1/2 : ℝ) < |x|) : gM M x = 0 := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  unfold gM
  rw [w_support M (by omega) _ (by
    rw [abs_mul, abs_of_pos hm]
    nlinarith [mul_pos hm (sub_pos.mpr hx)]) , mul_zero]

theorem actual_gM_zero_right {M : ℕ} (hM : 3 ≤ M) {x : ℝ}
    (hx : (1/2 : ℝ) ≤ x) : gM M x = 0 := by
  have hclosed : IsClosed {y : ℝ | gM M y = 0} :=
    isClosed_eq (actual_gM_continuous hM) continuous_const
  have hsub : Ioi (1/2 : ℝ) ⊆ {y : ℝ | gM M y = 0} := by
    intro y hy
    exact actual_gM_zero_outside hM (by
      rw [abs_of_nonneg (by linarith [mem_Ioi.mp hy])]
      exact hy)
  apply hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ioi]
  exact hx

theorem actual_gM_zero_closed_outside {M : ℕ} (hM : 3 ≤ M) {x : ℝ}
    (hx : (1/2 : ℝ) ≤ |x|) : gM M x = 0 := by
  rcases le_total 0 x with hp | hn
  · rw [abs_of_nonneg hp] at hx
    exact actual_gM_zero_right hM hx
  · rw [abs_of_nonpos hn] at hx
    rw [← actual_gM_even (by omega : 2 ≤ M) x]
    exact actual_gM_zero_right hM hx

theorem actual_deriv_zero_right_strict {M : ℕ} (hM : 4 ≤ M) {x : ℝ}
    (hx : (1/2 : ℝ) < x) : deriv (gM M) x = 0 := by
  have he : (fun _ : ℝ => (0 : ℝ)) =ᶠ[𝓝 x] gM M := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (actual_gM_zero_right (by omega : 3 ≤ M) hy.le).symm
  exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he.symm).deriv

theorem actual_deriv_zero_right {M : ℕ} (hM : 4 ≤ M) {x : ℝ}
    (hx : (1/2 : ℝ) ≤ x) : deriv (gM M) x = 0 := by
  have hc : IsClosed {y : ℝ | deriv (gM M) y = 0} :=
    isClosed_eq (actual_gM_deriv_continuous hM) continuous_const
  have hsub : Ioi (1/2 : ℝ) ⊆ {y : ℝ | deriv (gM M) y = 0} :=
    fun y hy => actual_deriv_zero_right_strict hM hy
  apply hc.closure_subset_iff.mpr hsub
  rw [closure_Ioi]
  exact hx

theorem actual_deriv_zero_closed_outside {M : ℕ} (hM : 4 ≤ M) {x : ℝ}
    (hx : (1/2 : ℝ) ≤ |x|) : deriv (gM M) x = 0 := by
  rcases le_total 0 x with hp | hn
  · rw [abs_of_nonneg hp] at hx
    exact actual_deriv_zero_right hM hx
  · rw [abs_of_nonpos hn] at hx
    have h := actual_deriv_zero_right hM hx
    rw [actual_gM_deriv_odd (by omega : 2 ≤ M)] at h
    linarith

theorem weighted_log_deriv_global {M : ℕ} (hM : 4 ≤ M) (x : ℝ) :
    |deriv (φM M) x| * gM M x = |deriv (gM M) x| / (M : ℝ) := by
  have hm : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  by_cases hx : |x| < (1/2 : ℝ)
  · rw [actual_gM_log_deriv (by omega : 3 ≤ M) (abs_lt.mp hx),
      abs_mul, abs_mul, abs_neg, abs_of_nonneg hm.le,
      abs_of_nonneg (actual_gM_nonneg M x)]
    field_simp [hm.ne'] <;> ring
  · rw [actual_gM_zero_closed_outside (by omega : 3 ≤ M) (le_of_not_gt hx),
      actual_deriv_zero_closed_outside hM (le_of_not_gt hx)]
    simp

theorem closed_deriv_nonpos {M : ℕ} (hM : 4 ≤ M) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1/2)) : deriv (gM M) x ≤ 0 := by
  rcases lt_or_eq_of_le hx.2 with hlt | he
  · exact actual_gM_deriv_nonpos (by omega : 3 ≤ M) ⟨hx.1, hlt⟩
  · rw [he, actual_deriv_zero_right hM (le_refl (1/2 : ℝ))]

theorem closed_antitone {M : ℕ} (hM : 3 ≤ M)
    {s b : ℝ} (hs : 0 ≤ s) (hb : b ≤ 1/2) :
    AntitoneOn (gM M) (Icc s b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc s b)
    (actual_gM_continuous hM).continuousOn
  · intro x _
    exact (hasDerivAt_gM hM x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact actual_gM_deriv_nonpos hM
      ⟨le_trans hs hx.1.le, lt_of_lt_of_le hx.2 hb⟩

theorem second_tail_closed_support (M k : ℕ) (hM : 4 ≤ M)
    (pk pk1 : ℝ → ℝ) {s r b c : ℝ}
    (hs : 0 ≤ s) (hsr : s < r) (hrb : r ≤ b) (hb : b ≤ 1 / 2)
    (hscale : 1 ≤ (M : ℝ) * (r - s))
    (hpk : Continuous pk) (hpk1 : Continuous pk1)
    (hLegPlus : ∀ x ∈ Icc r b,
      pk x ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk y ^ 2)
    (hLegPlus1 : ∀ x ∈ Icc r b,
      pk1 x ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk1 y ^ 2)
    (hLegMinus : ∀ x ∈ Icc r b,
      pk (-x) ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk (-y) ^ 2)
    (hLegMinus1 : ∀ x ∈ Icc r b,
      pk1 (-x) ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk1 (-y) ^ 2)
    (hTailPlus : ∫ y in s..b, pk y ^ 2 * gM M y ≤ Real.exp (-c*(M:ℝ)))
    (hTailPlus1 : ∫ y in s..b, pk1 y ^ 2 * gM M y ≤ Real.exp (-c*(M:ℝ)))
    (hTailMinus : ∫ y in s..b, pk (-y) ^ 2 * gM M (-y) ≤ Real.exp (-c*(M:ℝ)))
    (hTailMinus1 : ∫ y in s..b, pk1 (-y) ^ 2 * gM M (-y) ≤ Real.exp (-c*(M:ℝ))) :
    (∫ x in r..b, |pk x * pk1 x| * (-(deriv (gM M) x) / (M : ℝ))) +
      (∫ x in r..b, |pk (-x) * pk1 (-x)| *
        (-(-(deriv (gM M) (-x))) / (M : ℝ)))
      ≤ 2 * ((k:ℝ)+1)^2 * Real.exp (-c*(M:ℝ)) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hgPlus : ∀ x ∈ Icc s b,
      HasDerivAt (gM M) (deriv (gM M) x) x := by
    intro x hx
    convert (hasDerivAt_gM (by omega : 3 ≤ M) x) using 1
    exact (hasDerivAt_gM (by omega : 3 ≤ M) x).deriv
  have hgMinus : ∀ x ∈ Icc s b,
      HasDerivAt (fun y : ℝ => gM M (-y))
        (-(deriv (gM M) (-x))) x :=
    fun x _ => actual_reflected_hasDerivAt (by omega : 3 ≤ M) x
  have hc := actual_gM_deriv_continuous hM
  have hiPlus : IntervalIntegrable (deriv (gM M)) volume r b :=
    hc.intervalIntegrable r b
  have hiMinus : IntervalIntegrable
      (fun x : ℝ => -(deriv (gM M) (-x))) volume r b :=
    ((hc.comp continuous_neg).neg).intervalIntegrable r b
  have hmonoPlus : AntitoneOn (gM M) (Icc s b) :=
    closed_antitone (by omega : 3 ≤ M) hs hb
  have hmonoMinus : AntitoneOn (fun x : ℝ => gM M (-x)) (Icc s b) :=
    by
    intro x hx y hy hxy
    simpa only [actual_gM_even (by omega : 2 ≤ M)] using
      (closed_antitone (by omega : 3 ≤ M) hs hb) hx hy hxy
  have hnegPlus : ∀ x ∈ Icc r b, deriv (gM M) x ≤ 0 := by
    intro x hx
    exact closed_deriv_nonpos (by omega : 4 ≤ M)
      ⟨by linarith [hs, hsr, hx.1], le_trans hx.2 hb⟩
  have hnegMinus : ∀ x ∈ Icc r b, -(deriv (gM M) (-x)) ≤ 0 := by
    intro x hx
    rw [actual_gM_deriv_odd (by omega : 2 ≤ M), neg_neg]
    exact closed_deriv_nonpos (by omega : 4 ≤ M)
      ⟨by linarith [hs, hsr, hx.1], le_trans hx.2 hb⟩
  exact UniformLanczos.Lemma513ReflectedTails.two_reflected_tails
    pk pk1 (gM M) (deriv (gM M)) k hsr hrb hMpos hscale
    hpk hpk1 hgPlus hgMinus hiPlus hiMinus
    hmonoPlus hmonoMinus (actual_gM_nonneg M b)
    (actual_gM_nonneg M (-b)) hnegPlus hnegMinus
    hLegPlus hLegPlus1 hLegMinus hLegMinus1
    hTailPlus hTailPlus1 hTailMinus hTailMinus1

theorem original_signed_closed_tails (M k : ℕ) (hM : 4 ≤ M)
    (pk pk1 : ℝ → ℝ) {s r b c : ℝ}
    (hs : 0 ≤ s) (hsr : s < r) (hrb : r ≤ b) (hb : b ≤ 1 / 2)
    (hscale : 1 ≤ (M : ℝ) * (r - s))
    (hpk : Continuous pk) (hpk1 : Continuous pk1)
    (hLegPlus : ∀ x ∈ Icc r b,
      pk x ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk y ^ 2)
    (hLegPlus1 : ∀ x ∈ Icc r b,
      pk1 x ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk1 y ^ 2)
    (hLegMinus : ∀ x ∈ Icc r b,
      pk (-x) ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk (-y) ^ 2)
    (hLegMinus1 : ∀ x ∈ Icc r b,
      pk1 (-x) ^ 2 ≤ ((k:ℝ)+1)^2/(x-s) * ∫ y in s..x, pk1 (-y) ^ 2)
    (hTailPlus : ∫ y in s..b, pk y ^ 2 * gM M y ≤ Real.exp (-c*(M:ℝ)))
    (hTailPlus1 : ∫ y in s..b, pk1 y ^ 2 * gM M y ≤ Real.exp (-c*(M:ℝ)))
    (hTailMinus : ∫ y in s..b, pk (-y) ^ 2 * gM M (-y) ≤ Real.exp (-c*(M:ℝ)))
    (hTailMinus1 : ∫ y in s..b, pk1 (-y) ^ 2 * gM M (-y) ≤ Real.exp (-c*(M:ℝ))) :
    (∫ x in -b..-r,
      |pk x * pk1 x| * |deriv (φM M) x| * gM M x) +
    (∫ x in r..b,
      |pk x * pk1 x| * |deriv (φM M) x| * gM M x)
      ≤ 2 * ((k:ℝ)+1)^2 * Real.exp (-c*(M:ℝ)) := by
  have hM3 : 3 ≤ M := by omega
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  let F : ℝ → ℝ := fun x =>
    |pk x * pk1 x| * |deriv (φM M) x| * gM M x
  have hPlus : ∀ x ∈ Icc r b,
      |pk x * pk1 x| * (-(deriv (gM M) x) / (M : ℝ)) = F x := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hs, hsr, hx.1]
    rw [← abs_of_nonpos (closed_deriv_nonpos hM ⟨hx0, le_trans hx.2 hb⟩)]
    dsimp [F]
    rw [mul_assoc, weighted_log_deriv_global hM]
  have hMinus : ∀ x ∈ Icc r b,
      |pk (-x) * pk1 (-x)| * (-(-(deriv (gM M) (-x))) / (M : ℝ)) =
        F (-x) := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hs, hsr, hx.1]
    have hn : 0 ≤ deriv (gM M) (-x) := by
      rw [actual_gM_deriv_odd (by omega : 2 ≤ M)]
      exact neg_nonneg.mpr (closed_deriv_nonpos hM ⟨hx0, le_trans hx.2 hb⟩)
    rw [neg_neg, ← abs_of_nonneg hn]
    dsimp [F]
    rw [mul_assoc, weighted_log_deriv_global hM]
  have hplus_integral :
    (∫ x in r..b,
      |pk x * pk1 x| * (-(deriv (gM M) x) / (M : ℝ))) =
      ∫ x in r..b, F x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hrb] at hx
    exact hPlus x hx
  have hminus_integral :
    (∫ x in r..b,
      |pk (-x) * pk1 (-x)| *
        (-(-(deriv (gM M) (-x))) / (M : ℝ))) =
      ∫ x in -b..-r, F x := by
    calc
      (∫ x in r..b,
        |pk (-x) * pk1 (-x)| *
          (-(-(deriv (gM M) (-x))) / (M : ℝ)))
        = ∫ x in r..b, F (-x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          rw [uIcc_of_le hrb] at hx
          exact hMinus x hx
      _ = ∫ x in -b..-r, F x :=
        actual_left_reflection F r b
  have hMain := second_tail_closed_support M k hM pk pk1
    hs hsr hrb hb hscale hpk hpk1
    hLegPlus hLegPlus1 hLegMinus hLegMinus1
    hTailPlus hTailPlus1 hTailMinus hTailMinus1
  rw [hplus_integral, hminus_integral] at hMain
  change (∫ x in -b..-r, F x) + (∫ x in r..b, F x) ≤ _
  calc
    (∫ x in -b..-r, F x) + (∫ x in r..b, F x)
      = (∫ x in r..b, F x) + (∫ x in -b..-r, F x) := add_comm _ _
    _ ≤ 2 * ((k:ℝ)+1)^2 * Real.exp (-c*(M:ℝ)) := hMain


/-- Continuous weighted integrand even at the two support endpoints. -/
theorem weighted_integrand_continuous (M : ℕ) (hM : 4 ≤ M)
    (p q : ℝ → ℝ) (hp : Continuous p) (hq : Continuous q) :
    Continuous (fun x => |p x * q x| * |deriv (φM M) x| * gM M x) := by
  have he : (fun x => |p x * q x| * |deriv (φM M) x| * gM M x) =
      fun x => |p x * q x| * (|deriv (gM M) x| / (M : ℝ)) := by
    funext x
    rw [mul_assoc, weighted_log_deriv_global hM]
  rw [he]
  exact (hp.mul hq).abs.mul ((actual_gM_deriv_continuous hM).abs.div_const _)

theorem continuous_supported_integrable (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ x, (1/2 : ℝ) < |x| → f x = 0) : Integrable f := by
  have he : (Icc (-(1/2 : ℝ)) (1/2)).indicator f = f := by
    funext x
    by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
    · simp [hx]
    · have hxa : (1/2 : ℝ) < |x| := by
        by_contra! h
        exact hx (abs_le.mp h)
      simp [hx, hz x hxa]
  rw [← he, integrable_indicator_iff measurableSet_Icc]
  exact hf.continuousOn.integrableOn_compact isCompact_Icc

/-- The set integral on the original unbounded tail equals the two closed
support intervals. Lebesgue measure gives no mass to their endpoints. -/
theorem support_tail_split (f : ℝ → ℝ) (hf : Continuous f)
    (hz : ∀ x, (1/2 : ℝ) < |x| → f x = 0)
    {r : ℝ} (hr : 0 < r) (hrb : r ≤ 1/2) :
    (∫ x in {x : ℝ | r ≤ |x|}, f x) =
      (∫ x in -(1/2 : ℝ)..-r, f x) + (∫ x in r..(1/2 : ℝ), f x) := by
  let A : Set ℝ := Icc (-(1/2 : ℝ)) (-r)
  let B : Set ℝ := Icc r (1/2)
  have hA : MeasurableSet A := measurableSet_Icc
  have hB : MeasurableSet B := measurableSet_Icc
  have hT : MeasurableSet {x : ℝ | r ≤ |x|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hEq : ({x : ℝ | r ≤ |x|} : Set ℝ).indicator f = (A ∪ B).indicator f := by
    funext x
    by_cases hx : |x| ≤ (1/2 : ℝ)
    · have he : (r ≤ |x|) ↔ x ∈ A ∪ B := by
        rw [mem_union]
        rcases le_total 0 x with hp | hn
        · rw [abs_of_nonneg hp] at hx ⊢
          simp only [A, B, mem_Icc]
          constructor <;> intro h
          · exact Or.inr ⟨h,hx⟩
          · rcases h with h | h
            · linarith [h.2]
            · exact h.1
        · rw [abs_of_nonpos hn] at hx ⊢
          simp only [A, B, mem_Icc]
          constructor <;> intro h
          · exact Or.inl ⟨by linarith, by linarith⟩
          · rcases h with h | h
            · linarith [h.2]
            · linarith [h.1]
      by_cases ht : r ≤ |x|
      · simp [ht, he.mp ht]
      · simp [ht, fun h => ht (he.mpr h)]
    · simp [hz x (lt_of_not_ge hx)]
  have hd : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x ha hb
    have ha' : x ≤ -r := ha.2
    have hb' : r ≤ x := hb.1
    linarith
  have hi := continuous_supported_integrable f hf hz
  calc
    _ = ∫ x in A ∪ B, f x := by
      rw [← MeasureTheory.integral_indicator hT, ← MeasureTheory.integral_indicator (hA.union hB), hEq]
    _ = (∫ x in A, f x) + (∫ x in B, f x) :=
      setIntegral_union hd hB hi.integrableOn hi.integrableOn
    _ = _ := by
      dsimp [A,B]
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le (by linarith : -(1/2 : ℝ) ≤ -r),
        intervalIntegral.integral_of_le hrb]

/-- A common index threshold controls both the scale factor and the preceding
index in the fixed enlarged proportional interval. -/
theorem uniform_scale_previous {t₁ t₂ s r : ℝ} (ht₁ : 0 < t₁)
    (hsr : s < r) (L : ℕ) :
    ∃ N : ℕ, L ≤ N ∧ 4 ≤ N ∧ ∀ M k : ℕ, N ≤ M →
      (k : ℝ)/(M : ℝ) ∈ Icc t₁ t₂ →
      1 ≤ (M : ℝ)*(r-s) ∧
      (k : ℝ)/(M : ℝ) ∈ Icc (t₁/2) t₂ ∧
      ((k-1 : ℕ) : ℝ)/(M : ℝ) ∈ Icc (t₁/2) t₂ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1/(r-s)) (2/t₁))
  let N := max (max L 4) n
  refine ⟨N, by dsimp [N]; omega, by dsimp [N]; omega, ?_⟩
  intro M k hM hk
  have hMn : n ≤ M := by dsimp [N] at hM; omega
  have hc : (n : ℝ) ≤ M := by exact_mod_cast hMn
  have hM4 : 4 ≤ M := by dsimp [N] at hM; omega
  have hp : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have h1 : 1/(r-s) < (M : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hn) hc
  have h2 : 2/t₁ < (M : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hn) hc
  have hscale : 1 ≤ (M : ℝ)*(r-s) := ((div_lt_iff₀ (sub_pos.mpr hsr)).mp h1).le
  have hlarge : 2 < (M : ℝ)*t₁ := (div_lt_iff₀ ht₁).mp h2
  have hklo : t₁*(M : ℝ) ≤ k := (le_div_iff₀ hp).mp hk.1
  have hkpos : 1 ≤ k := by
    by_contra! h
    have hkzero : k = 0 := by omega
    rw [hkzero, Nat.cast_zero] at hklo
    nlinarith
  have hprev : ((k-1 : ℕ) : ℝ) = (k : ℝ)-1 := by exact Nat.cast_sub hkpos
  refine ⟨hscale, ⟨by linarith [hk.1], hk.2⟩, ?_⟩
  constructor
  · apply (le_div_iff₀ hp).mpr
    rw [hprev]
    nlinarith
  · apply (div_le_iff₀ hp).mpr
    rw [hprev]
    have hu := (div_le_iff₀ hp).mp hk.2
    linarith

end UniformLanczos.Lemma513SupportUniform

#print axioms UniformLanczos.Lemma513SupportUniform.actual_gM_zero_closed_outside
#print axioms UniformLanczos.Lemma513SupportUniform.actual_deriv_zero_closed_outside
#print axioms UniformLanczos.Lemma513SupportUniform.weighted_log_deriv_global
#print axioms UniformLanczos.Lemma513SupportUniform.second_tail_closed_support
#print axioms UniformLanczos.Lemma513SupportUniform.original_signed_closed_tails
#print axioms UniformLanczos.Lemma513SupportUniform.weighted_integrand_continuous
#print axioms UniformLanczos.Lemma513SupportUniform.continuous_supported_integrable
#print axioms UniformLanczos.Lemma513SupportUniform.support_tail_split
#print axioms UniformLanczos.Lemma513SupportUniform.uniform_scale_previous
