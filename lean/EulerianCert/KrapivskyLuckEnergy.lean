import EulerianCert.Energy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Manuscripts 11 and 12, 2026-11-15: sine-integral energy identities

The actual radius and sine integral are those of EulerianCert.FourierModes.
The already-proved primitive in EulerianCert.Energy is reused, not postulated.
The real-line total-energy identity is isolated as the classical Plancherel
input for the tail statements; no statement about prime-zeta regularisation
is inferred.
-/

open Real MeasureTheory intervalIntegral Set
open EulerianCert.FourierModes EulerianCert.Energy

noncomputable section

namespace Manuscripts11And12.KrapivskyLuck

/-- M12 (56b), for every positive endpoint (including the removable origin). -/
theorem integral_half (a : ℝ) (ha : 0 < a) :
    (∫ t in (0 : ℝ)..a, rE t ^ 2) =
      2 * Si a - 2 * (1 - Real.cos a) / a := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.le continuous_G.continuousOn
    (fun t ht => hasDerivAt_G ht.1.ne') ((continuous_rE.pow 2).intervalIntegrable _ _)]
  simp only [G, Si, intervalIntegral.integral_same, mul_zero, zero_div, sinc_zero,
    zero_mul, sub_zero]
  have hc := Real.cos_two_mul (a / 2)
  rw [show 2 * (a / 2) = a by ring] at hc
  have hs := Real.sin_sq_add_cos_sq (a / 2)
  have htrig : 2 * Real.sin (a / 2) ^ 2 = 1 - Real.cos a := by
    nlinarith
  have hboundary : a * sinc (a / 2) ^ 2 = 2 * (1 - Real.cos a) / a := by
    rw [sinc_of_ne_zero (div_ne_zero ha.ne' two_ne_zero), ← htrig]
    field_simp [ha.ne'] <;> ring
  rw [hboundary]

theorem integral_symmetric (a : ℝ) :
    (∫ t in (-a)..a, rE t ^ 2) = 2 * ∫ t in (0 : ℝ)..a, rE t ^ 2 := by
  have hc : Continuous (fun t => rE t ^ 2) := continuous_rE.pow 2
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := a)
    (fun t => rE t ^ 2)
  simp only [neg_zero, rE_neg] at h
  rw [← h]
  ring

/-- M11 (48a), arbitrary positive window, not a periodic continuation. -/
theorem extended_energy (a : ℝ) (ha : 0 < a) :
    (1 / (2 * a)) * (∫ t in (-a)..a, rE t ^ 2) =
      (2 / a) * Si a - 2 * (1 - Real.cos a) / a ^ 2 := by
  rw [integral_symmetric, integral_half a ha]
  field_simp [ha.ne'] <;> ring

/-- Linear integral with the actual removable sinc profile. -/
theorem integral_linear (b : ℝ) :
    (∫ t in (0 : ℝ)..b, rE t) = 2 * Si (b / 2) := by
  calc
    _ = ∫ t in (0 : ℝ)..b, sinc ((1 / 2 : ℝ) * t) := by
      apply intervalIntegral.integral_congr
      intro t _
      unfold rE
      rw [show t / 2 = (1 / 2 : ℝ) * t by ring]
    _ = _ := by
      rw [intervalIntegral.integral_comp_mul_left _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      simp [Si, smul_eq_mul, div_eq_mul_inv, mul_comm]

def C : ℝ := Si (2 * π) / π
def S : ℝ := 1 / 2 - C

/-- M11 (48b), the linear identity. -/
theorem C_linear :
    C = (1 / (2 * π)) * (∫ t in (0 : ℝ)..(4 * π), rE t) := by
  rw [integral_linear, show 4 * π / 2 = 2 * π by ring, C]
  field_simp [pi_ne_zero]

/-- M11 (48b), the quadratic identity. -/
theorem C_energy :
    C = (1 / (4 * π)) * (∫ t in (-(2 * π))..(2 * π), rE t ^ 2) := by
  rw [integral_symmetric, integral_half _ (by positivity), Real.cos_two_pi, C]
  field_simp [pi_ne_zero] <;> ring

/-- Closed central window versus interval integral (endpoints have zero mass). -/
theorem C_energy_set :
    C = (1 / (4 * π)) * (∫ t in Icc (-(2 * π)) (2 * π), rE t ^ 2) := by
  rw [C_energy, integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith [pi_pos])]

/-- The real representative of the normalized Paley--Wiener kernel at zero. -/
def k0 (t : ℝ) : ℝ := rE t / Real.sqrt (2 * π)

theorem k0_sq (t : ℝ) : |k0 t| ^ 2 = (1 / (2 * π)) * rE t ^ 2 := by
  rw [sq_abs, k0, div_pow, Real.sq_sqrt (by positivity)]
  ring

/-- M12 (56a), expressed using the real representative of the normalized kernel. -/
theorem C_normalized_energy :
    C = (1 / 2) * (∫ t in Icc (-(2 * π)) (2 * π), |k0 t| ^ 2) := by
  simp_rw [k0_sq, MeasureTheory.integral_const_mul]
  rw [C_energy_set]
  ring

theorem tail_set :
    {t : ℝ | 2 * π < |t|} = (Icc (-(2 * π)) (2 * π))ᶜ := by
  ext t
  change 2 * π < |t| ↔ ¬ (-(2 * π) ≤ t ∧ t ≤ 2 * π)
  rw [← abs_le, not_le]

/-- M11 (48c), given the separately cited real-line Plancherel normalization.
Integrability follows since the specified Bochner integral is nonzero. -/
theorem S_tail (htotal : (∫ t : ℝ, rE t ^ 2) = 2 * π) :
    S = (1 / (4 * π)) * (∫ t in {t : ℝ | 2 * π < |t|}, rE t ^ 2) := by
  have hi : Integrable (fun t : ℝ => rE t ^ 2) := by
    by_contra h
    rw [integral_undef h] at htotal
    linarith [pi_pos]
  rw [tail_set, setIntegral_compl measurableSet_Icc hi, htotal, S, C_energy_set]
  field_simp [pi_ne_zero] <;> ring

/-- M12 (56c), the squared tail energy, with the same explicit Plancherel input. -/
theorem S_normalized_tail (htotal : (∫ t : ℝ, rE t ^ 2) = 2 * π) :
    S = (1 / 2) * (∫ t in {t : ℝ | 2 * π < |t|}, |k0 t| ^ 2) := by
  simp_rw [k0_sq, MeasureTheory.integral_const_mul]
  rw [S_tail htotal]
  ring

end Manuscripts11And12.KrapivskyLuck

#print axioms Manuscripts11And12.KrapivskyLuck.integral_half
#print axioms Manuscripts11And12.KrapivskyLuck.integral_symmetric
#print axioms Manuscripts11And12.KrapivskyLuck.extended_energy
#print axioms Manuscripts11And12.KrapivskyLuck.integral_linear
#print axioms Manuscripts11And12.KrapivskyLuck.C_linear
#print axioms Manuscripts11And12.KrapivskyLuck.C_energy
#print axioms Manuscripts11And12.KrapivskyLuck.C_energy_set
#print axioms Manuscripts11And12.KrapivskyLuck.k0_sq
#print axioms Manuscripts11And12.KrapivskyLuck.C_normalized_energy
#print axioms Manuscripts11And12.KrapivskyLuck.tail_set
#print axioms Manuscripts11And12.KrapivskyLuck.S_tail
#print axioms Manuscripts11And12.KrapivskyLuck.S_normalized_tail
