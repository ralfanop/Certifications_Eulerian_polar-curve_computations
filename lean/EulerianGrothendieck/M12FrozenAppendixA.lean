import Bridge.AppendixA
import Bridge.AppendixAGd
import Bridge.AppendixAMoments

/-! Frozen M12 (18 Nov 2026), Appendix A, equations (279)–(293).
Source SHA256 7ae7cd218e77c42ecbae087cd4c3c6b79890abf38a0faf312111bae5c5608860.
This module uses the audited Bridge proofs and states the printed
subtraction/division and integral-series forms explicitly. -/

open Real MeasureTheory Set intervalIntegral
open EulerianBridge.AppendixA

namespace M12FrozenAppendixA

/-- (281), natural-number subtraction as printed, shifted from k ≥ 2. -/
theorem eq281 (k : ℕ) : a (k + 2) = 8 * a (k + 1) - 16 * a k := by
  have h := a_rec k
  omega

/-- (282), actual moments summed to the integral claimed in the text. -/
theorem eq282_integral_sum :
    HasSum m (∫ t in (-1/2:ℝ)..(1/2), (1 - t ^ 2)⁻¹) := by
  rw [integral_inv_one_sub_sq]
  have h := moments_sum.1
  rw [moments_sum.2.2] at h
  have hm : m = (fun k : ℕ => 1 / ((4 : ℝ) ^ k * (2 * (k : ℝ) + 1))) :=
    funext m_eq
  rw [hm]
  exact h

/-- (288), the real-valued division form of the central binomial identity. -/
theorem eq288 (k : ℕ) :
    (Nat.choose (2*k) k : ℝ) = (2:ℝ)^k * (oddDF k:ℝ) / (k.factorial:ℝ) := by
  rw [← Nat.centralBinom_eq_two_mul_choose]
  apply (eq_div_iff (by positivity)).2
  have h : (k.factorial:ℝ) * (Nat.centralBinom k:ℝ) =
      (2:ℝ)^k * (oddDF k:ℝ) := by
    exact_mod_cast central_binom_semifactorial k
  rw [mul_comm]
  exact h

/-- (289), both equalities in the printed Catalan formula. -/
theorem eq289 (k : ℕ) :
    (catalan k:ℝ) = (Nat.choose (2*k) k:ℝ) / ((k:ℝ)+1) ∧
    (catalan k:ℝ) = (2:ℝ)^k * (oddDF k:ℝ) / ((k+1).factorial:ℝ) := by
  constructor
  · rw [← Nat.centralBinom_eq_two_mul_choose]
    apply (eq_div_iff (by positivity)).2
    have h : ((k:ℝ)+1) * (catalan k:ℝ) = (Nat.centralBinom k:ℝ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom k
    rw [mul_comm]
    exact h
  · apply (eq_div_iff (by positivity)).2
    have h : ((k+1).factorial:ℝ) * (catalan k:ℝ) =
        (2:ℝ)^k * (oddDF k:ℝ) := by
      exact_mod_cast catalan_semifactorial k
    rw [mul_comm]
    exact h

end M12FrozenAppendixA

#print axioms M12FrozenAppendixA.eq281
#print axioms M12FrozenAppendixA.eq282_integral_sum
#print axioms M12FrozenAppendixA.eq288
#print axioms M12FrozenAppendixA.eq289

-- Preserve explicit links to the previously audited source declarations.
#check EulerianBridge.AppendixA.a_ogf
#check EulerianBridge.AppendixA.a_egf
#check EulerianBridge.AppendixA.moments_sum
#check EulerianBridge.AppendixA.gd
#check EulerianBridge.AppendixA.gd_strictMono
#check EulerianBridge.AppendixA.range_gd
#check EulerianBridge.AppendixA.gdInv
#check EulerianBridge.AppendixA.gdInv_eq_log_tan
#check EulerianBridge.AppendixA.gdInv_eq_arctanh_sin
#check EulerianBridge.AppendixA.gdInv_gd
#check EulerianBridge.AppendixA.gd_gdInv
#check EulerianBridge.AppendixA.gdInv_pi_div_four
#check EulerianBridge.AppendixA.gdInv_arctan_four_thirds
#check EulerianBridge.AppendixA.m_semifactorial
#check EulerianBridge.AppendixA.uniform_moments
#check EulerianBridge.AppendixA.arcsine_moment
#check EulerianBridge.AppendixA.semicircle_moment
#check EulerianBridge.AppendixA.gaussian_moment
