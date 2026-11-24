import UniformLanczos.Lemma513ActualGM
import Mathlib

/-!
# Manuscript 12 Lemma 5.13 — original signed-domain weighted integral

Completes the *real integration-variable transfer* missing from the abstract
two-reflected-tails proof and its actual g_M weight specialization.

On both compact endpoint intervals within (-1/2,1/2), the derived identity
    g_M' = -M g_M phi_M'
transforms the derivative-weight integrands into the actual manuscript's
    |p_k p_{k-1}| |phi_M'| g_M.
Mathlib's exact intervalIntegral.integral_comp_neg maps the left reflected
integral on [r,b] to the ORIGINAL signed interval [-b,-r].

The Christoffel polynomial inequalities and the exponentially small first
tails are cited classical / previously proved inputs, NOT an assumption of
the second-tail conclusion. This module does not claim a global set-integral
over |x|>=r outside the compact support without an endpoint-support lemma.
-/

namespace UniformLanczos.Lemma513OriginalIntegral

open Set MeasureTheory intervalIntegral
open EulerianBridge.Saddle
open UniformLanczos.Lemma56
open UniformLanczos.Lemma513ActualGM

/-- Second inequality (158), on the two signed endpoint intervals, for the
actual cardinal B-spline g_M and actual logarithmic derivative phi_M'.

Unlike PR #522, the conclusion contains the literal signed-domain integrals
of the manuscript, not integrals of abstract reflected derivative weights. -/
theorem original_signed_two_tails (M k : ℕ) (hM : 4 ≤ M)
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
  have hphi_plus : ∀ x ∈ Icc r b, 0 ≤ deriv (φM M) x := by
    intro x hx
    exact actual_phi_deriv_nonneg hM3
      ⟨by linarith [hs, hsr, hx.1], by linarith [hb, hx.2]⟩
  have hPlus : ∀ x ∈ Icc r b,
      |pk x * pk1 x| * (-(deriv (gM M) x) / (M : ℝ)) = F x := by
    intro x hx
    have hxi : x ∈ Ioo (-(1/2:ℝ)) (1/2) :=
      ⟨by linarith [hs, hsr, hx.1], by linarith [hb, hx.2]⟩
    rw [actual_gM_log_deriv hM3 hxi]
    dsimp [F]
    rw [abs_of_nonneg (hphi_plus x hx)]
    field_simp [hMne] <;> ring
  have hMinus : ∀ x ∈ Icc r b,
      |pk (-x) * pk1 (-x)| * (-(-(deriv (gM M) (-x))) / (M : ℝ)) =
        F (-x) := by
    intro x hx
    have hxi : -x ∈ Ioo (-(1/2:ℝ)) (1/2) :=
      ⟨by linarith [hb, hx.2], by linarith [hs, hsr, hx.1]⟩
    have hphi_minus : deriv (φM M) (-x) ≤ 0 := by
      rw [deriv_φM_odd (by omega : 2 ≤ M) x]
      exact neg_nonpos.mpr (hphi_plus x hx)
    rw [actual_gM_log_deriv hM3 hxi]
    dsimp [F]
    rw [abs_of_nonpos hphi_minus]
    field_simp [hMne] <;> ring
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
  have hMain := second_tail_actual_gM M k hM pk pk1
    hs hsr hrb hb hscale hpk hpk1
    hLegPlus hLegPlus1 hLegMinus hLegMinus1
    hTailPlus hTailPlus1 hTailMinus hTailMinus1
  rw [hplus_integral, hminus_integral] at hMain
  change (∫ x in -b..-r, F x) + (∫ x in r..b, F x) ≤ _
  calc
    (∫ x in -b..-r, F x) + (∫ x in r..b, F x)
      = (∫ x in r..b, F x) + (∫ x in -b..-r, F x) := add_comm _ _
    _ ≤ 2 * ((k:ℝ)+1)^2 * Real.exp (-c*(M:ℝ)) := hMain

end UniformLanczos.Lemma513OriginalIntegral

#print axioms UniformLanczos.Lemma513OriginalIntegral.original_signed_two_tails
