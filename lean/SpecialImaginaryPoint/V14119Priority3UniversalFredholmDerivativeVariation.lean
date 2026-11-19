import SpecialImaginaryPoint.FredholmCauchyEstimates
import SpecialImaginaryPoint.V14119Priority3UniversalFredholmRobustNonvanishing
import SpecialImaginaryPoint.V14119Priority3UniversalFredholmEntire

/-!
# Quantitative derivative and logarithmic-derivative stability

This closes gate F1 in the Fredholm dossier of 2026-11-19. All determinant
functions here are the actual finite-compression limits on the repository's
genuine CFC Schatten-S₁ ideal over `H = ℓ²(ℕ, ℂ)`.

No normality, selfadjointness, positivity, eigenvalue enumeration, trace
formula, or bound on a derivative difference is assumed. Cauchy's estimate
is applied to `u ↦ D_T(z+u) - D_S(w+u)`. The translation leaves `z-w`
unchanged, so the already proved joint determinant bound supplies an
explicit bound for the derivative difference.

These are classical consequences of the certified determinant estimates,
not claims of mathematical novelty. They do not prove the separate
trace-resolvent formula or the Fredholm invertibility equivalence.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmDerivativeVariation

open Complex Metric
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.UniversalFredholmSpectralVariation
open Manuscript14Priority3.UniversalFredholmJointVariation
open Manuscript14Priority3.UniversalFredholmRobustNonvanishing
open Manuscript14Priority3.FredholmCauchyEstimates

/-- Explicit bound for the simultaneous operator/spectral derivative change.
The theorem below requires `ρ > 0`. -/
def jointFredholmDerivativeError
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ) (ρ : ℝ) : ℝ :=
  (((‖z‖ + ρ) * ‖T - S‖) *
      Real.exp ((‖z‖ + ρ) * (‖S‖ + ‖T - S‖)) +
    (‖z - w‖ * ‖S‖) *
      Real.exp ((‖w‖ + ρ + ‖z - w‖) * ‖S‖)) / ρ

/-- A Cauchy derivative bound using increments from the centre. -/
def fredholmDerivativeBound
    (S : ProbabilisticTheory.TraceClass H) (w : ℂ) (ρ : ℝ) : ℝ :=
  ‖S‖ * Real.exp ((‖w‖ + ρ) * ‖S‖)

theorem universalFredholm_joint_deriv_diff_norm_le
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ‖deriv (fredholmDet T) z - deriv (fredholmDet S) w‖ ≤
      jointFredholmDerivativeError T S z w ρ := by
  apply translated_deriv_sub_norm_le (fredholmDet T) (fredholmDet S)
    (universal_fredholmDet_entire T) (universal_fredholmDet_entire S)
    z w ρ _ hρ
  intro u hu
  have hu' : ‖u‖ = ρ := by simpa only [mem_sphere, dist_zero_right] using hu
  have hz : ‖z + u‖ ≤ ‖z‖ + ρ := by simpa only [hu'] using norm_add_le z u
  have hw : ‖w + u‖ ≤ ‖w‖ + ρ := by simpa only [hu'] using norm_add_le w u
  have hzw : (z + u) - (w + u) = z - w := by ring
  have h := universalFredholm_joint_diff_norm_le T S (z + u) (w + u)
  rw [hzw] at h
  refine h.trans (add_le_add ?_ ?_)
  · apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hz (add_nonneg (norm_nonneg _) (norm_nonneg _)))
    · exact (Real.exp_pos _).le
    · exact mul_nonneg (add_nonneg (norm_nonneg _) hρ.le) (norm_nonneg _)
  · apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (add_le_add_right hw _) (norm_nonneg _))

/-- In particular, the dossier's requested fixed-parameter estimate holds. -/
theorem universalFredholm_two_operators_deriv_diff_norm_le
    (T S : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ‖deriv (fredholmDet T) z - deriv (fredholmDet S) z‖ ≤
      (((‖z‖ + ρ) * ‖T - S‖) *
        Real.exp ((‖z‖ + ρ) * (‖S‖ + ‖T - S‖))) / ρ := by
  simpa [jointFredholmDerivativeError] using
    universalFredholm_joint_deriv_diff_norm_le T S z z ρ hρ

/-- The derivative of the reference determinant is bounded explicitly too. -/
theorem universalFredholm_deriv_norm_le
    (S : ProbabilisticTheory.TraceClass H) (w : ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ‖deriv (fredholmDet S) w‖ ≤ fredholmDerivativeBound S w ρ := by
  have h := translated_deriv_norm_le (fredholmDet S)
    (universal_fredholmDet_entire S) w ρ
    ((ρ * ‖S‖) * Real.exp ((‖w‖ + ρ) * ‖S‖)) hρ (by
      intro u hu
      have hu' : ‖u‖ = ρ := by simpa only [mem_sphere, dist_zero_right] using hu
      have heq : w + u - w = u := by ring
      simpa only [heq, hu'] using
        universalFredholm_spectral_diff_norm_le S (w + u) w)
  have heq : ((ρ * ‖S‖) * Real.exp ((‖w‖ + ρ) * ‖S‖)) / ρ =
      fredholmDerivativeBound S w ρ := by
    unfold fredholmDerivativeBound
    field_simp [ne_of_gt hρ]
    <;> ring
  rwa [heq] at h

/-- Fully explicit logarithmic-derivative stability. The strict determinant
margin implies nonvanishing of both determinants; no derivative bound is
left as a hypothesis, and no perturbed denominator remains on the RHS. -/
theorem universalFredholm_joint_logDeriv_explicit_bound_of_margin
    (T S : ProbabilisticTheory.TraceClass H) (z w : ℂ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hmargin : jointFredholmError T S z w < ‖fredholmDet S w‖) :
    ‖logDeriv (fredholmDet T) z - logDeriv (fredholmDet S) w‖ ≤
      jointFredholmDerivativeError T S z w ρ /
        (‖fredholmDet S w‖ - jointFredholmError T S z w) +
      (fredholmDerivativeBound S w ρ * jointFredholmError T S z w) /
        ((‖fredholmDet S w‖ - jointFredholmError T S z w) * ‖fredholmDet S w‖) := by
  exact quotient_difference_le_of_margin
    (deriv (fredholmDet T) z) (deriv (fredholmDet S) w)
    (fredholmDet T z) (fredholmDet S w)
    (jointFredholmError T S z w) (jointFredholmDerivativeError T S z w ρ)
    (fredholmDerivativeBound S w ρ)
    (universalFredholm_joint_diff_norm_le T S z w)
    (universalFredholm_joint_deriv_diff_norm_le T S z w ρ hρ)
    (universalFredholm_deriv_norm_le S w ρ hρ) hmargin

#print axioms universalFredholm_joint_deriv_diff_norm_le
#print axioms universalFredholm_two_operators_deriv_diff_norm_le
#print axioms universalFredholm_deriv_norm_le
#print axioms universalFredholm_joint_logDeriv_explicit_bound_of_margin

end Manuscript14Priority3.UniversalFredholmDerivativeVariation
