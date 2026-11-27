import CriticalWindowGammaVacuum
import CrossNormalization20261126

/-! M12 DOUBLE_RADICAL, p. 74, equation (364).
The actual F(0), the 40th positive real root, and the two nested square
roots. The certified Gamma quadrature is reused without recomputation. -/
namespace M12Radical364
open MeasureTheory

noncomputable def radicalProfile (u : ℝ) : ℝ :=
  1 / (Real.exp (u^4)) ^ ((1:ℝ)/40)

theorem radical_profile_eq (u : ℝ) :
    radicalProfile u = M12CriticalGamma.quarticProfile u := by
  unfold radicalProfile M12CriticalGamma.quarticProfile
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, one_div, ← Real.exp_neg]
  congr 1
  ring

theorem fourth_root_factor :
    (40:ℝ)^((1:ℝ)/4) = 2 * Real.sqrt (Real.sqrt (5/2)) := by
  let a : ℝ := (40:ℝ)^((1:ℝ)/4)
  let b : ℝ := 2 * Real.sqrt (Real.sqrt (5/2))
  have ha : 0 < a := Real.rpow_pos_of_pos (by norm_num) _
  have hb : 0 < b := by dsimp [b]; positivity
  have ha4 : a^4 = 40 := by
    dsimp [a]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 40)]
    norm_num
  have hb4 : b^4 = 40 := by
    have hb2 : b^2 = 4 * Real.sqrt (5/2) := by
      dsimp [b]
      rw [mul_pow, Real.sq_sqrt (Real.sqrt_nonneg (5/2))]
      norm_num
    calc
      b^4 = (b^2)^2 := by ring
      _ = 40 := by
        rw [hb2, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5/2)]
        norm_num
  have hzero : (a-b)*((a+b)*(a^2+b^2)) = 0 := by
    calc
      _ = a^4-b^4 := by ring
      _ = 0 := by rw [ha4,hb4]; ring
  have hpos : 0 < (a+b)*(a^2+b^2) := by positivity
  have h := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hpos)
  exact sub_eq_zero.mp h

theorem radical_profile_integrable : Integrable radicalProfile := by
  have h : radicalProfile = M12CriticalGamma.quarticProfile := funext radical_profile_eq
  rw [h]
  exact M12CriticalGamma.quarticProfile_integrable

theorem actual_F_zero_radical :
    M12CriticalDCT.F 0 =
      (1/(2*Real.sqrt Real.pi)) * (∫ u : ℝ, radicalProfile u) := by
  unfold M12CriticalDCT.F
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    rw [radical_profile_eq]
    simp [M12CriticalDCT.profile, M12CriticalGamma.quarticProfile]

theorem radical_integral_gamma :
    (1/(2*Real.sqrt Real.pi)) * (∫ u : ℝ, radicalProfile u) =
      Real.sqrt (Real.sqrt (5/2)) * (Real.Gamma (1/4)/(2*Real.sqrt Real.pi)) := by
  have h : radicalProfile = M12CriticalGamma.quarticProfile := funext radical_profile_eq
  rw [h, M12CriticalGamma.critical_constant, fourth_root_factor]
  have hs : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp [hs] <;> ring

theorem equation_364 :
    M12CriticalDCT.F 0 =
      Real.sqrt (Real.sqrt (5/2)) * (Real.Gamma (1/4)/(2*Real.sqrt Real.pi)) :=
  actual_F_zero_radical.trans radical_integral_gamma

theorem binary_selfdual_radical :
    M12CrossNormalization.binaryZ (1/Real.sqrt 2) =
      (Real.sqrt (Real.sqrt (5/2)) * (Real.Gamma (1/4)/(2*Real.sqrt Real.pi)))^2 := by
  rw [M12CrossNormalization.binaryZ_selfdual, equation_364]

end M12Radical364

#print axioms M12Radical364.radical_profile_eq
#print axioms M12Radical364.fourth_root_factor
#print axioms M12Radical364.radical_profile_integrable
#print axioms M12Radical364.actual_F_zero_radical
#print axioms M12Radical364.radical_integral_gamma
#print axioms M12Radical364.equation_364
#print axioms M12Radical364.binary_selfdual_radical
