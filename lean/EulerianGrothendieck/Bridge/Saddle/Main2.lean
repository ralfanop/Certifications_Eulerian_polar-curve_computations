import Bridge.Saddle.Main

/-!
# Lemma 5.5 (manuscript V173), final assembly

`lemma_5_5`: for every `b ∈ (0, 1/2)` there are `M₀`, `C` such that for `M ≥ M₀` and `|x| ≤ b`,
with `E_M = log g_M + MI - ½ log(M/(2πv)) - η/M`,
`|E_M(x)|, |E_M'(x)|, |E_M''(x)| ≤ C/(M√M)`   (eq. (68)).
-/

open MeasureTheory Set Complex Filter Topology Metric
open scoped Nat

namespace EulerianBridge.Saddle

/-- `ε = M^{-1/2}`. -/
noncomputable def epsM (M : ℕ) : ℝ := (Real.sqrt M)⁻¹

theorem epsM_pos {M : ℕ} (hM : 1 ≤ M) : 0 < epsM M := by
  unfold epsM; have : (0:ℝ) < M := by exact_mod_cast hM
  positivity

theorem epsM_sq {M : ℕ} (hM : 1 ≤ M) : (M:ℝ) * epsM M ^ 2 = 1 := by
  unfold epsM; have : (0:ℝ) < M := by exact_mod_cast hM
  rw [inv_pow, Real.sq_sqrt this.le]; field_simp

theorem epsM_cube {M : ℕ} (hM : 1 ≤ M) : epsM M ^ 3 = 1 / (M * Real.sqrt M) := by
  unfold epsM
  have h : (0:ℝ) < M := by exact_mod_cast hM
  have hs : Real.sqrt M ^ 2 = M := Real.sq_sqrt h.le
  rw [inv_pow, one_div]; congr 1; rw [pow_succ, hs]

/-- The normalisation `c = √κ₂ / √(2π)`. -/
noncomputable def cN (s : ℝ) : ℝ := Real.sqrt (κ 2 s) / Real.sqrt (2 * Real.pi)

theorem cN_pos (s : ℝ) : 0 < cN s := by
  unfold cN; have := κ_two_pos s; have := Real.pi_pos; positivity

theorem cN_mul_sqrt (s : ℝ) : cN s * Real.sqrt (2 * Real.pi / κ 2 s) = 1 := by
  unfold cN
  have hk := κ_two_pos s
  have hp : 0 < 2 * Real.pi := by positivity
  rw [Real.sqrt_div' _ hk.le]
  have h1 : 0 < Real.sqrt (κ 2 s) := Real.sqrt_pos.mpr hk
  have h2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hp
  field_simp

/-- The normalised integrals `Y_r = c I_r`. -/
noncomputable def Yr (s : ℝ) (M r : ℕ) : ℂ := (cN s : ℂ) * Ir s M (epsM M) r

theorem Ar_pow_eq (s : ℝ) (M : ℕ) (x : ℝ) :
    Ar s ^ M * Real.exp (-(s * M * x)) = Real.exp (M * (Lr s - s * x)) := by
  have : Ar s ^ M = Real.exp (M * Lr s) := by
    rw [Lr, ← Real.exp_log (Ar_pos s)]; rw [Real.log_exp, ← Real.exp_nat_mul]
  rw [this, ← Real.exp_add]; ring_nf

/-- Pointwise identities expressing `g_M`, `E_M'`, `E_M''` through the `Y_r`. -/
theorem pt_identities {M : ℕ} (hM : 4 ≤ M) {x : ℝ} (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (hY0 : Yr (UL.Ip x) M 0 ≠ 0) :
    ∃ y0 : ℝ, (y0 : ℂ) = Yr (UL.Ip x) M 0 ∧
      gM M x = y0 * (Real.sqrt M / (Real.sqrt (2 * Real.pi) * Real.sqrt (κ 2 (UL.Ip x)))) *
        Real.exp (M * (Lr (UL.Ip x) - UL.Ip x * x)) ∧
      ((E1 M x : ℝ) : ℂ) = -((epsM M : ℂ)⁻¹ * (Yr (UL.Ip x) M 1 / Yr (UL.Ip x) M 0)) +
        (L1 (UL.Ip x) : ℂ) - (epsM M : ℂ) ^ 2 * (eta1 (UL.Ip x) : ℂ) ∧
      ((E2 M x : ℝ) : ℂ) = ((epsM M : ℂ) ^ 2)⁻¹ * (Yr (UL.Ip x) M 2 / Yr (UL.Ip x) M 0 -
        (Yr (UL.Ip x) M 1 / Yr (UL.Ip x) M 0) ^ 2 - G20 (UL.Ip x)) + (L2 (UL.Ip x) : ℂ) -
        (epsM M : ℂ) ^ 2 * (eta2 (UL.Ip x) : ℂ) := by
  have hM1 : 1 ≤ M := by omega
  have hx' : κ 1 (UL.Ip x) = x := Lp_Ip' hx
  unfold E1 E2 gM
  generalize hs : UL.Ip x = s at *
  have he0 : 0 < epsM M := epsM_pos hM1
  have hMe : (M:ℝ) * epsM M ^ 2 = 1 := epsM_sq hM1
  generalize hev : epsM M = e at *
  obtain ⟨W0, W1, W2⟩ := w_repr hM hx' he0
  have hP : 0 < Ar s ^ M * Real.exp (-(s * M * x)) := by have := Ar_pos s; positivity
  have hc : 0 < cN s := cN_pos s
  have hY : ∀ r, Yr s M r = (cN s : ℂ) * Ir s M e r := by intro r; rw [Yr, hev]
  have hI0 : Ir s M e 0 ≠ 0 := by intro h; apply hY0; rw [hY, h, mul_zero]
  have hcC : (cN s : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hPC : ((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have heC : (e:ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have hpiC : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have hMC : (M:ℂ) = ((e:ℂ) ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left (by exact_mod_cast hMe)
  have hw0 : (w M (M * x) : ℂ) ≠ 0 := by
    rw [W0]; exact mul_ne_zero (mul_ne_zero (inv_ne_zero hpiC) hPC) (mul_ne_zero heC hI0)
  refine ⟨w M (M * x) * (2 * Real.pi * cN s) / ((Ar s ^ M * Real.exp (-(s * M * x))) * e), ?_, ?_, ?_, ?_⟩
  · rw [hY]
    have : (((w M (M * x) * (2 * Real.pi * cN s) / ((Ar s ^ M * Real.exp (-(s * M * x))) * e)) : ℝ) : ℂ) =
        (w M (M * x) : ℂ) * (2 * Real.pi * (cN s : ℂ)) /
          (((Ar s ^ M * Real.exp (-(s * M * x)) : ℝ) : ℂ) * (e:ℂ)) := by push_cast; ring
    rw [this, W0]
    field_simp
  · -- g_M through y0
    have hPe : Ar s ^ M * Real.exp (-(s * M * x)) = Real.exp (M * (Lr s - s * x)) := Ar_pow_eq s M x
    rw [← hPe]
    have hMpos : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hsMpos : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
    have hs2pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hkpos : 0 < Real.sqrt (κ 2 s) := Real.sqrt_pos.mpr (κ_two_pos s)
    have hs2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
    have heM : e = (Real.sqrt M)⁻¹ := by rw [← hev]; rfl
    have hsM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hMpos.le
    have hs2' : Real.sqrt (Real.pi * 2) ^ 2 = Real.pi * 2 := Real.sq_sqrt (by positivity)
    have hAr : Ar s ≠ 0 := (Ar_pos s).ne'
    have hAM : Ar s ^ M * (Ar s)⁻¹ ^ M = 1 := by rw [← mul_pow, mul_inv_cancel₀ hAr, one_pow]
    rw [heM]
    simp only [cN]
    field_simp
    simp only [hsM, hs2, hs2']
    try ring_nf
    try (rw [hAM]; ring)
    try (simp only [hAM]; ring)
    try (nlinarith [hAM])
  · -- E1
    have hratio : ((deriv (w M) (M * x) : ℝ) : ℂ) / ((w M (M * x) : ℝ) : ℂ) =
        -(s:ℂ) - (e:ℂ) * (Ir s M e 1 / Ir s M e 0) := by
      rw [W0, W1]; field_simp; try ring
    push_cast
    rw [hratio, hY, hY, hMC]
    field_simp
    ring
  · -- E2
    have hr1 : ((deriv (w M) (M * x) : ℝ) : ℂ) / ((w M (M * x) : ℝ) : ℂ) =
        -(s:ℂ) - (e:ℂ) * (Ir s M e 1 / Ir s M e 0) := by
      rw [W0, W1]; field_simp; try ring
    have hr2 : ((deriv (deriv (w M)) (M * x) : ℝ) : ℂ) / ((w M (M * x) : ℝ) : ℂ) =
        (s:ℂ) ^ 2 + 2 * (s:ℂ) * ((e:ℂ) * (Ir s M e 1 / Ir s M e 0)) + (e:ℂ) ^ 2 * (Ir s M e 2 / Ir s M e 0) := by
      rw [W0, W2]; field_simp; try ring
    push_cast
    rw [hr1, hr2, hY, hY, hY, hMC]
    have hk : ((κ 2 s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast κ2_ne s
    simp only [G20, kc]
    field_simp
    ring

/-- `E_M = log y₀ - η/M` once `y₀ > 0`. -/
theorem EM_eq {M : ℕ} (hM : 1 ≤ M) {x y0 : ℝ} (hy0 : 0 < y0)
    (hg : gM M x = y0 * (Real.sqrt M / (Real.sqrt (2 * Real.pi) * Real.sqrt (κ 2 (UL.Ip x)))) *
      Real.exp (M * (Lr (UL.Ip x) - UL.Ip x * x))) :
    EM M x = Real.log y0 - etaS (UL.Ip x) / M := by
  set s := UL.Ip x
  have hMpos : (0:ℝ) < M := by exact_mod_cast hM
  have hk := κ_two_pos s
  have hp : 0 < 2 * Real.pi := by positivity
  have h1 : 0 < Real.sqrt M := Real.sqrt_pos.mpr hMpos
  have h2 : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr hp
  have h3 : 0 < Real.sqrt (κ 2 s) := Real.sqrt_pos.mpr hk
  unfold EM
  rw [hg, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_div h1.ne' (by positivity), Real.log_mul h2.ne' h3.ne',
    Real.log_sqrt hMpos.le, Real.log_sqrt hp.le, Real.log_sqrt hk.le]
  unfold Irate vx etaX
  rw [Real.log_div hMpos.ne' (by positivity), Real.log_mul hp.ne' hk.ne']
  ring

theorem log_bound {y : ℝ} (hy : |y - 1| ≤ 1 / 2) : |Real.log y - (y - 1)| ≤ 2 * (y - 1) ^ 2 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 - y) (by rw [abs_sub_comm]; linarith) 1
  simp only [Finset.sum_range_one, zero_add, pow_one, Nat.cast_zero, div_one, sub_sub_cancel] at h
  have habs : |1 - y| = |y - 1| := abs_sub_comm _ _
  rw [habs] at h
  have hd : 0 < 1 - |y - 1| := by linarith
  have : |y - 1| ^ (1 + 1) / (1 - |y - 1|) ≤ 2 * (y - 1) ^ 2 := by
    rw [div_le_iff₀ hd, show (1 + 1 : ℕ) = 2 by rfl, sq_abs]
    nlinarith [sq_nonneg (y - 1)]
  have h' : |Real.log y - (y - 1)| = |1 - y + Real.log y| := by
    congr 1; ring
  rw [h']
  exact h.trans this

end EulerianBridge.Saddle
