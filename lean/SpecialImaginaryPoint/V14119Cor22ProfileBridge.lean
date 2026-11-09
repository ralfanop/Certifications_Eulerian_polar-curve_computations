import SpecialImaginaryPoint.V14119SpecialValueBridge
import SpecialImaginaryPoint.V14119Cor22Certificate

/-!
# Manuscript 14.119, complete connection of Corollary 2.2 to the profile

This file identifies the purely imaginary special-point parameter and combines
the genuine analytic Eulerian profile with the all-N strict factorial-series
tail certificate. It adds no scalar assumptions or external numerical oracles.
-/

namespace SpecialImaginaryPoint.V14119Cor22Profile

/-- Our analytic test point is literally z_0 = i/sqrt(2). -/
theorem specialPoint_eq_z0 :
    V14119SpecialValue.specialPoint =
      Complex.I / (((Real.sqrt (2 : ℝ)) : ℂ)) := by
  have hsqrt : Real.sqrt (8 : ℝ) = 2 * Real.sqrt (2 : ℝ) := by
    calc
      Real.sqrt (8 : ℝ) = Real.sqrt (4 * 2 : ℝ) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 2 :=
        Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ)) (2 : ℝ)
      _ = 2 * Real.sqrt 2 := by norm_num
  have hroot : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hrootC : (((Real.sqrt (2 : ℝ)) : ℂ)) ≠ 0 := by
    exact_mod_cast hroot
  dsimp [V14119SpecialValue.specialPoint]
  rw [hsqrt]
  push_cast
  field_simp [hrootC] <;> ring

/-- Both strict bounds of Corollary 2.2 hold for the genuine complex Eulerian
profile at z_0, for every natural N. -/
theorem eulerian_profile_corollary22 (N : ℕ) :
    V14119Cor22.prefixSum N <
      (EulerianSpecialPoint.eulerianEvenAnalytic
        V14119SpecialValue.specialPoint).re ∧
    (EulerianSpecialPoint.eulerianEvenAnalytic
        V14119SpecialValue.specialPoint).re <
      V14119Cor22.prefixSum N +
      V14119Cor22.coeff (N + 1) / (1 - V14119Cor22.ratio (N + 1)) := by
  have hprofile :
      (∑' n : ℕ, V14119Cor22.coeff n) =
        (EulerianSpecialPoint.eulerianEvenAnalytic
          V14119SpecialValue.specialPoint).re := by
    have h :=
      congrArg Complex.re V14119SpecialValue.eulerian_profile_special_series
    simpa only [Complex.ofReal_re, V14119Cor22.coeff] using h.symm
  have h := V14119Cor22.rational_tail_bound N
  simpa only [hprofile] using h

#print axioms SpecialImaginaryPoint.V14119Cor22Profile.specialPoint_eq_z0
#print axioms SpecialImaginaryPoint.V14119Cor22Profile.eulerian_profile_corollary22

end SpecialImaginaryPoint.V14119Cor22Profile
