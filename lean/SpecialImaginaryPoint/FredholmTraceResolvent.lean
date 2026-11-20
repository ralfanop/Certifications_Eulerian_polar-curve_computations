import SharedCore.ResolventRingIdentities
import SpecialImaginaryPoint.FredholmMultiplicativity
import SpecialImaginaryPoint.FredholmActualTrace

/-!
# The genuine Fredholm trace-resolvent formula

For the actual CFC trace ideal on H = ℓ²(ℕ, ℂ), invertibility of
I + zT implies nonvanishing of the actual Fredholm determinant, and

  D_T'(z) / D_T(z) = Tr(T (I + zT)⁻¹).

The trace was defined independently by an absolutely summable Hilbert
basis diagonal. Multiplicativity and a noncommutative resolvent
factorisation transfer the derivative-at-zero theorem to arbitrary
resolvent points. No normality, selfadjointness, diagonalisation,
spectral enumeration or a stipulated trace formula is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Manuscript14Priority3.FredholmTraceResolvent
open scoped Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmComplexScaleCovariance
open Manuscript14Priority3.FredholmMultiplicativity
open Manuscript14Priority3.ActualTrace
open ProbabilisticTheory.TraceClass
open SharedCore.ResolventRingIdentities

def inversePerturbation (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ProbabilisticTheory.TraceClass H :=
  -(sandwichContinuous (1 + z • T.1)⁻¹ʳ 1 (z • T))

theorem inversePerturbation_product (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    inversePerturbation T z + z • T + inversePerturbation T z * (z • T) = 0 := by
  apply Subtype.ext
  change -((1 + z • T.1)⁻¹ʳ * (z • T.1) * 1) + z • T.1 +
      (-((1 + z • T.1)⁻¹ʳ * (z • T.1) * 1)) * (z • T.1) = 0
  simpa only [mul_one] using inverse_perturbation_product (z • T.1) hz

/-- Invertibility implies nonvanishing, proved from genuine multiplicativity. -/
theorem fredholmDet_ne_zero_of_isUnit (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : IsUnit (1 + z • T.1)) : fredholmDet T z ≠ 0 := by
  have hm := fredholmDet_multiplicative (inversePerturbation T z) (z • T)
  rw [inversePerturbation_product T z hz, fredholmDet_zero_operator,
    ← universalFredholm_spectral_smul T z] at hm
  intro hzero
  rw [hzero, mul_zero] at hm
  exact one_ne_zero hm

/-- The actual trace-class resolvent product T (I + zT)⁻¹. -/
def rightResolvent (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ProbabilisticTheory.TraceClass H :=
  sandwichContinuous 1 (1 + z • T.1)⁻¹ʳ T

theorem rightResolvent_operator (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    (rightResolvent T z).1 = T.1 * (1 + z • T.1)⁻¹ʳ := by
  change 1 * T.1 * (1 + z • T.1)⁻¹ʳ = _
  rw [one_mul]

theorem rightResolvent_product (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    rightResolvent T z + rightResolvent T z * (z • T) = T := by
  apply Subtype.ext
  change (rightResolvent T z).1 + (rightResolvent T z).1 * (z • T.1) = T.1
  rw [rightResolvent_operator]
  exact right_resolvent_product (z • T.1) T.1 hz

theorem shifted_product (T : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    w • rightResolvent T z + z • T +
        (w • rightResolvent T z) * (z • T) = (w + z) • T := by
  calc
    _ = w • (rightResolvent T z + rightResolvent T z * (z • T)) + z • T := by
      rw [smul_add, smul_mul_assoc]
      abel
    _ = (w + z) • T := by rw [rightResolvent_product T z hz, add_smul]

theorem fredholm_shift_factor (T : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    fredholmDet T (w + z) = fredholmDet (rightResolvent T z) w * fredholmDet T z := by
  calc
    _ = fredholmDet ((w + z) • T) 1 := universalFredholm_spectral_smul T (w + z)
    _ = fredholmDet (w • rightResolvent T z + z • T +
        (w • rightResolvent T z) * (z • T)) 1 := by rw [shifted_product T z w hz]
    _ = fredholmDet (w • rightResolvent T z) 1 * fredholmDet (z • T) 1 :=
      fredholmDet_multiplicative _ _
    _ = _ := by rw [← universalFredholm_spectral_smul, ← universalFredholm_spectral_smul]

/-- The genuine derivative at every actual resolvent point. -/
theorem fredholm_deriv_eq_trace_mul (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    deriv (fredholmDet T) z = actualTrace (rightResolvent T z) * fredholmDet T z := by
  have hf : (fun w : ℂ => fredholmDet T (w + z)) =
      (fun w : ℂ => fredholmDet (rightResolvent T z) w * fredholmDet T z) :=
    funext (fun w => fredholm_shift_factor T z w hz)
  have hd := congrArg (fun f : ℂ → ℂ => deriv f 0) hf
  simpa only [deriv_comp_add_const, zero_add, deriv_mul_const_field,
    fredholm_deriv_zero_eq_actualTrace] using hd

/-- Full trace-resolvent identity for arbitrary nonnormal CFC trace-class T. -/
theorem fredholm_logDeriv_eq_actualTrace (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    deriv (fredholmDet T) z / fredholmDet T z = actualTrace (rightResolvent T z) := by
  rw [fredholm_deriv_eq_trace_mul T z hz]
  exact mul_div_cancel_right₀ _ (fredholmDet_ne_zero_of_isUnit T z hz)

theorem fredholm_logDeriv_norm_le (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : IsUnit (1 + z • T.1)) :
    ‖deriv (fredholmDet T) z / fredholmDet T z‖ ≤ ‖T‖ * ‖(1 + z • T.1)⁻¹ʳ‖ := by
  rw [fredholm_logDeriv_eq_actualTrace T z hz]
  calc
    _ ≤ ‖rightResolvent T z‖ := actualTrace_norm_le _
    _ ≤ ‖sandwichContinuous 1 (1 + z • T.1)⁻¹ʳ‖ * ‖T‖ :=
      (sandwichContinuous 1 (1 + z • T.1)⁻¹ʳ).le_opNorm T
    _ ≤ (‖(1 : H →L[ℂ] H)‖ * ‖(1 + z • T.1)⁻¹ʳ‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right (sandwichContinuous_norm_le _ _) (norm_nonneg _)
    _ = _ := by simp [mul_comm]

#print axioms inversePerturbation_product
#print axioms fredholmDet_ne_zero_of_isUnit
#print axioms rightResolvent_operator
#print axioms rightResolvent_product
#print axioms shifted_product
#print axioms fredholm_shift_factor
#print axioms fredholm_deriv_eq_trace_mul
#print axioms fredholm_logDeriv_eq_actualTrace
#print axioms fredholm_logDeriv_norm_le
end Manuscript14Priority3.FredholmTraceResolvent
