import UniformLanczos.Lemma513ReflectedTails
import UniformLanczos.Lemma56
import Mathlib

/-!
# Manuscript 12, Lemma 5.13 — the actual B-spline weight g_M

This is the *missing weight-specialisation*, as distinct from the abstract
one- and two-sided endpoint estimates already certified in PR #511/#522.

The weight is the existing actual definition
  EulerianBridge.Saddle.gM M x = M * w M (M*x),
and phi_M = -log(g_M)/M is the existing analytic definition.
From the published/previously proved B-spline regularity and strict
log-concavity in Lemma 5.6 we derive the derivative identity,
positive-half-line monotonicity and its reflected counterpart.

Only the *classical* endpoint Christoffel inequalities and the
previously proved exponential first tails are explicit premises of
the final bound. No assumption asserts the original second tail.
-/

namespace UniformLanczos.Lemma513ActualGM

open Set MeasureTheory intervalIntegral
open EulerianBridge.Saddle
open UniformLanczos.Lemma56

theorem actual_gM_even {M : ℕ} (hM : 2 ≤ M) (x : ℝ) :
    gM M (-x) = gM M x := by
  change (M : ℝ) * w M ((M : ℝ) * -x) =
    (M : ℝ) * w M ((M : ℝ) * x)
  rw [mul_neg, UniformLanczos.Joined.w_even M hM]

theorem actual_gM_nonneg (M : ℕ) (x : ℝ) : 0 ≤ gM M x := by
  unfold gM
  exact mul_nonneg (Nat.cast_nonneg M) (w_nonneg M _)

theorem actual_gM_deriv_odd {M : ℕ} (hM : 2 ≤ M) (x : ℝ) :
    deriv (gM M) (-x) = -deriv (gM M) x := by
  have heq : (fun y => gM M (-y)) = gM M := funext (actual_gM_even hM)
  have hd : deriv (fun y => gM M (-y)) x = -deriv (gM M) (-x) :=
    deriv_comp_neg (gM M) x
  rw [heq] at hd
  linarith

/-- The *actual* logarithmic derivative identity, not an extra premise:
g_M'(x) = -M g_M(x) phi_M'(x) for |x| < 1/2, M >= 3. -/
theorem actual_gM_log_deriv {M : ℕ} (hM : 3 ≤ M) {x : ℝ}
    (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    deriv (gM M) x = -(M : ℝ) * gM M x * deriv (φM M) x := by
  have hw : 0 < w M ((M : ℝ) * x) :=
    w_scaled_pos (by omega : 2 ≤ M) hx
  rw [(hasDerivAt_gM hM x).deriv,
    (hasDerivAt_φM_three hM hw).deriv]
  change (M : ℝ) * (deriv (w M) ((M : ℝ) * x) * (M : ℝ)) =
    -(M : ℝ) * ((M : ℝ) * w M ((M : ℝ) * x)) *
      (-(deriv (w M) ((M : ℝ) * x) / w M ((M : ℝ) * x)))
  field_simp [hw.ne'] <;> ring

theorem actual_phi_deriv_nonneg {M : ℕ} (hM : 3 ≤ M)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    0 ≤ deriv (φM M) x := by
  have hzero : deriv (φM M) 0 = 0 := deriv_φM_zero (by omega)
  by_cases hx0 : x = 0
  · subst x
    simpa only [hzero] using (le_refl (0 : ℝ))
  · have hxgt : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hmem : (0 : ℝ) ∈ Ico (0 : ℝ) (1 / 2) := ⟨le_rfl, by norm_num⟩
    have h := (lemma_5_6_hm hM) hmem hx hxgt
    rw [hzero] at h
    exact h.le

theorem actual_gM_deriv_nonpos {M : ℕ} (hM : 3 ≤ M)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    deriv (gM M) x ≤ 0 := by
  have hInt : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨by linarith [hx.1], hx.2⟩
  rw [actual_gM_log_deriv hM hInt]
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hpos := actual_gM_nonneg M x
  have hφ := actual_phi_deriv_nonneg hM hx
  calc
    -(M : ℝ) * gM M x * deriv (φM M) x
        = -((M : ℝ) * gM M x * deriv (φM M) x) := by ring
    _ ≤ 0 := neg_nonpos.mpr (mul_nonneg (mul_nonneg hM0 hpos) hφ)

theorem actual_gM_continuous {M : ℕ} (hM : 3 ≤ M) :
    Continuous (gM M) :=
  continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_gM hM x).continuousAt)

theorem actual_gM_antitone {M : ℕ} (hM : 3 ≤ M)
    {s b : ℝ} (hs : 0 ≤ s) (hb : b < 1 / 2) :
    AntitoneOn (gM M) (Icc s b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc s b)
    (actual_gM_continuous hM).continuousOn
  · intro x _
    exact (hasDerivAt_gM hM x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hxs : s < x := (mem_Ioo.mp hx).1
    have hxb : x < b := (mem_Ioo.mp hx).2
    exact actual_gM_deriv_nonpos hM
      ⟨le_trans hs hxs.le, lt_trans hxb hb⟩

theorem actual_gM_reflected_antitone {M : ℕ} (hM : 3 ≤ M)
    {s b : ℝ} (hs : 0 ≤ s) (hb : b < 1 / 2) :
    AntitoneOn (fun x : ℝ => gM M (-x)) (Icc s b) := by
  intro x hx y hy hxy
  simpa only [actual_gM_even (by omega : 2 ≤ M)] using
    (actual_gM_antitone hM hs hb) hx hy hxy

theorem actual_gM_deriv_continuous {M : ℕ} (hM : 4 ≤ M) :
    Continuous (deriv (gM M)) := by
  have heq : deriv (gM M) =
    (fun x : ℝ => (M : ℝ) * (deriv (w M) ((M : ℝ) * x) * (M : ℝ))) :=
      funext (fun x => (hasDerivAt_gM (by omega : 3 ≤ M) x).deriv)
  rw [heq]
  exact continuous_const.mul
    (((continuous_deriv_w hM).comp
      (continuous_const.mul continuous_id)).mul continuous_const)

theorem actual_reflected_hasDerivAt {M : ℕ} (hM : 3 ≤ M) (x : ℝ) :
    HasDerivAt (fun y : ℝ => gM M (-y)) (-(deriv (gM M) (-x))) x := by
  have h : HasDerivAt (gM M) (deriv (gM M) x) x := by
    convert (hasDerivAt_gM hM x) using 1
    exact (hasDerivAt_gM hM x).deriv
  rw [show (fun y : ℝ => gM M (-y)) = gM M from
      funext (actual_gM_even (by omega : 2 ≤ M)),
      actual_gM_deriv_odd (by omega : 2 ≤ M) x, neg_neg]
  exact h

theorem actual_gM_reflected_deriv_nonpos {M : ℕ} (hM : 3 ≤ M)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) (1 / 2)) :
    -(deriv (gM M) (-x)) ≤ 0 := by
  rw [actual_gM_deriv_odd (by omega : 2 ≤ M)]
  simp only [neg_neg]
  exact actual_gM_deriv_nonpos hM hx

/-- Specialisation of the verified two-reflected-tail theorem to the ACTUAL
cardinal B-spline g_M. None of its analytic weight assumptions remains:
g_M derivatives, monotonicity, reflection, positivity and integrability are
proved above. The classic Christoffel inequalities and first-tail estimates
are the explicitly listed inputs. -/
theorem second_tail_actual_gM (M k : ℕ) (hM : 4 ≤ M)
    (pk pk1 : ℝ → ℝ) {s r b c : ℝ}
    (hs : 0 ≤ s) (hsr : s < r) (hrb : r ≤ b) (hb : b < 1 / 2)
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
    actual_gM_antitone (by omega : 3 ≤ M) hs hb
  have hmonoMinus : AntitoneOn (fun x : ℝ => gM M (-x)) (Icc s b) :=
    actual_gM_reflected_antitone (by omega : 3 ≤ M) hs hb
  have hnegPlus : ∀ x ∈ Icc r b, deriv (gM M) x ≤ 0 := by
    intro x hx
    apply actual_gM_deriv_nonpos (by omega : 3 ≤ M)
    exact ⟨by linarith [hs, hsr, hx.1], by linarith [hb, hx.2]⟩
  have hnegMinus : ∀ x ∈ Icc r b, -(deriv (gM M) (-x)) ≤ 0 := by
    intro x hx
    apply actual_gM_reflected_deriv_nonpos (by omega : 3 ≤ M)
    exact ⟨by linarith [hs, hsr, hx.1], by linarith [hb, hx.2]⟩
  exact UniformLanczos.Lemma513ReflectedTails.two_reflected_tails
    pk pk1 (gM M) (deriv (gM M)) k hsr hrb hMpos hscale
    hpk hpk1 hgPlus hgMinus hiPlus hiMinus
    hmonoPlus hmonoMinus (actual_gM_nonneg M b)
    (actual_gM_nonneg M (-b)) hnegPlus hnegMinus
    hLegPlus hLegPlus1 hLegMinus hLegMinus1
    hTailPlus hTailPlus1 hTailMinus hTailMinus1

/-- Ordinary left/right integral substitution. This is a direct Mathlib
change of variables; the left endpoint really is -b, not b. -/
theorem actual_left_reflection (f : ℝ → ℝ) (r b : ℝ) :
    (∫ x in r..b, f (-x)) = ∫ x in -b..-r, f x :=
  intervalIntegral.integral_comp_neg f

end UniformLanczos.Lemma513ActualGM

#print axioms UniformLanczos.Lemma513ActualGM.actual_gM_even
#print axioms UniformLanczos.Lemma513ActualGM.actual_gM_nonneg
#print axioms UniformLanczos.Lemma513ActualGM.actual_gM_deriv_odd
#print axioms UniformLanczos.Lemma513ActualGM.actual_gM_log_deriv
#print axioms UniformLanczos.Lemma513ActualGM.actual_phi_deriv_nonneg
#print axioms UniformLanczos.Lemma513ActualGM.actual_gM_deriv_nonpos
#print axioms UniformLanczos.Lemma513ActualGM.actual_gM_antitone
#print axioms UniformLanczos.Lemma513ActualGM.actual_reflected_hasDerivAt
#print axioms UniformLanczos.Lemma513ActualGM.second_tail_actual_gM
#print axioms UniformLanczos.Lemma513ActualGM.actual_left_reflection
