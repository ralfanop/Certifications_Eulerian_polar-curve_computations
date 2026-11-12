import SpecialImaginaryPoint.V14119Priority3UniversalFredholmRobustNonvanishing
import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLogDerivative

/-!
# Priority 3 — quantitative logarithmic-derivative stability reduction

This is a rigorous algebraic reduction for the genuine CFC Schatten-S₁
universal Fredholm determinant at two independently varying pairs (T,z)
and (S,w). It uses the exact two-variable determinant trace-norm
perturbation bound and the strictly positive margin from the preceding
module. It controls the difference of the genuine *complex* Fredholm
logarithmic derivatives by the difference of the **complex derivatives**
plus a fully explicit trace-class/spectral perturbation term.

The remaining mathematical obligation for an entirely explicit
trace-norm Lipschitz estimate is an independent bound on the
**derivative difference**. No such bound is smuggled in here.
This quotient estimate is classical algebra, not an originality claim.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmLogDerivStabilityBridge

open Filter Topology Set Complex
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmJointVariation
open Manuscript14Priority3.UniversalFredholmRobustNonvanishing

/-- Algebraic stability estimate for two complex quotients.
The nonzero hypotheses are actual denominator conditions, not
formal cancellations through a zero. -/
theorem complex_quotient_difference_norm_le
    (A B a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖A / a - B / b‖ ≤
      ‖A - B‖ / ‖a‖ + (‖B‖ * ‖a - b‖) / (‖a‖ * ‖b‖) := by
  have hdecomp :
      A / a - B / b = (A - B) / a - (B * (a - b)) / (a * b) := by
    field_simp [ha, hb]
    <;> ring
  calc
    ‖A / a - B / b‖ =
        ‖(A - B) / a - (B * (a - b)) / (a * b)‖ :=
      congrArg norm hdecomp
    _ ≤ ‖(A - B) / a‖ + ‖(B * (a - b)) / (a * b)‖ :=
      norm_sub_le _ _
    _ = ‖A - B‖ / ‖a‖ +
          (‖B‖ * ‖a - b‖) / (‖a‖ * ‖b‖) := by
      simp only [norm_div, norm_mul]

/-- For the true Fredholm determinants, the change of complex
logarithmic derivative is bounded by derivative variation and the
certified joint operator/spectral determinant error. -/
theorem universalFredholm_joint_logDeriv_diff_norm_le
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hT : fredholmDet T z ≠ 0)
    (hS : fredholmDet S w ≠ 0) :
    ‖logDeriv (fredholmDet T) z - logDeriv (fredholmDet S) w‖ ≤
      ‖deriv (fredholmDet T) z - deriv (fredholmDet S) w‖ /
        ‖fredholmDet T z‖ +
      (‖deriv (fredholmDet S) w‖ * jointFredholmError T S z w) /
        (‖fredholmDet T z‖ * ‖fredholmDet S w‖) := by
  have hq := complex_quotient_difference_norm_le
    (deriv (fredholmDet T) z) (deriv (fredholmDet S) w)
    (fredholmDet T z) (fredholmDet S w) hT hS
  have hvar : ‖fredholmDet T z - fredholmDet S w‖ ≤
      jointFredholmError T S z w :=
    universalFredholm_joint_diff_norm_le T S z w
  have hmul :
      ‖deriv (fredholmDet S) w‖ * ‖fredholmDet T z - fredholmDet S w‖ ≤
      ‖deriv (fredholmDet S) w‖ * jointFredholmError T S z w :=
    mul_le_mul_of_nonneg_left hvar (norm_nonneg _)
  have hdiv :
      (‖deriv (fredholmDet S) w‖ * ‖fredholmDet T z - fredholmDet S w‖) /
          (‖fredholmDet T z‖ * ‖fredholmDet S w‖) ≤
      (‖deriv (fredholmDet S) w‖ * jointFredholmError T S z w) /
          (‖fredholmDet T z‖ * ‖fredholmDet S w‖) := by
    simp only [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmul
      (inv_nonneg.mpr (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  calc
    ‖logDeriv (fredholmDet T) z - logDeriv (fredholmDet S) w‖ ≤
        ‖deriv (fredholmDet T) z - deriv (fredholmDet S) w‖ /
          ‖fredholmDet T z‖ +
        (‖deriv (fredholmDet S) w‖ * ‖fredholmDet T z - fredholmDet S w‖) /
          (‖fredholmDet T z‖ * ‖fredholmDet S w‖) := by
      change ‖deriv (fredholmDet T) z / fredholmDet T z -
        deriv (fredholmDet S) w / fredholmDet S w‖ ≤ _
      exact hq
    _ ≤ _ := add_le_add_right hdiv _

/-- The determinant nonvanishing conditions become automatic
inside the explicit strict joint perturbation margin. This yields
a well-defined Fredholm logarithmic-derivative comparison without
assuming nonvanishing of the perturbed determinant separately. -/
theorem universalFredholm_joint_logDeriv_bound_of_margin
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (hmargin : jointFredholmError T S z w < ‖fredholmDet S w‖) :
    ‖logDeriv (fredholmDet T) z - logDeriv (fredholmDet S) w‖ ≤
      ‖deriv (fredholmDet T) z - deriv (fredholmDet S) w‖ /
        ‖fredholmDet T z‖ +
      (‖deriv (fredholmDet S) w‖ * jointFredholmError T S z w) /
        (‖fredholmDet T z‖ * ‖fredholmDet S w‖) := by
  have hE : 0 ≤ jointFredholmError T S z w := by
    unfold jointFredholmError
    positivity
  have hS : fredholmDet S w ≠ 0 := by
    intro hz
    have hpos : 0 < ‖fredholmDet S w‖ :=
      lt_of_le_of_lt hE hmargin
    simp [hz] at hpos
  exact universalFredholm_joint_logDeriv_diff_norm_le T S z w
    (universalFredholm_joint_nonzero_of_margin T S z w hmargin) hS

#print axioms Manuscript14Priority3.FredholmLogDerivStabilityBridge.complex_quotient_difference_norm_le
#print axioms Manuscript14Priority3.FredholmLogDerivStabilityBridge.universalFredholm_joint_logDeriv_diff_norm_le
#print axioms Manuscript14Priority3.FredholmLogDerivStabilityBridge.universalFredholm_joint_logDeriv_bound_of_margin

end Manuscript14Priority3.FredholmLogDerivStabilityBridge
