import SpecialImaginaryPoint.V14119Priority3FredholmExplicitJensenBound
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Priority 3 — exponential-type growth and linear Jensen zero-count estimates

The *genuine* universal infinite-dimensional CFC Schatten-S₁ Fredholm
determinant f_T(z)=det_F(I+zT), for ANY complex trace-class Hilbert
operator T (even nonnormal, nonselfadjoint), satisfies the exact
normalization f_T(0)=1 and universal spectral-parameter variation
bound. From these, one derives the explicit global growth inequality

  ‖f_T(z)‖ ≤ exp(2 ‖z‖ ‖T‖).

Consequently the total divisor of genuine Fredholm determinant zeros,
counted with their algebraic/analytic orders in a smaller disk of radius r,
obeys the Jensen-type linear growth estimate

  N_T(r) ≤ 2 R ‖T‖ / log(R/r),  whenever 0 < r < R.

This verifies exponential-type order at most one in the elementary
global growth-bound sense, but does not claim optimal constants or
a sharp Fredholm determinant upper bound. Jensen's theorem is classical
and reused from Mathlib; only its application to the genuine
operatorial determinant is at issue here.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmLinearJensenGrowth

open Filter Topology Set Metric MeromorphicOn
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FredholmExplicitJensenBound
open Manuscript14Priority3.MeromorphicFredholmReciprocal

/-- True universal CFC-S₁ Fredholm determinant has an explicit global
exponential growth bound with type at most 2‖T‖. -/
theorem universalFredholm_norm_le_exp_two_traceNorm
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet T z‖ ≤
      Real.exp (2 * (‖z‖ * ‖T‖)) := by
  let x : ℝ := ‖z‖ * ‖T‖
  have hx : 0 ≤ x := mul_nonneg (norm_nonneg z) (norm_nonneg T)
  have hexp : 1 ≤ Real.exp x := by
    calc
      (1 : ℝ) ≤ x + 1 := by linarith
      _ ≤ Real.exp x := Real.add_one_le_exp x
  have hbase :
      1 + x * Real.exp x ≤ Real.exp (2 * x) := by
    calc
      1 + x * Real.exp x ≤ Real.exp x + x * Real.exp x :=
        add_le_add_left hexp _
      _ = (1 + x) * Real.exp x := by ring
      _ ≤ Real.exp x * Real.exp x :=
        mul_le_mul_of_nonneg_right
          (by simpa only [add_comm] using Real.add_one_le_exp x)
          (Real.exp_pos x).le
      _ = Real.exp (2 * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact (universalFredholm_norm_le_one_add_trace_exponential T z).trans
    (by simpa only [x] using hbase)

/-- True infinite-dimensional Fredholm divisor admits a completely
explicit linear-in-R upper estimate with no user-supplied outer-circle
modulus. It counts zeros with their actual analytic multiplicities. -/
theorem universalFredholm_Jensen_zero_count_linear_traceNorm_bound
    (T : ProbabilisticTheory.TraceClass H)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) r) u
      ≤ (2 * (R * ‖T‖)) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hM :
      (1 : ℝ) ≤ Real.exp (2 * (R * ‖T‖)) := by
    have hx : 0 ≤ 2 * (R * ‖T‖) := by positivity
    calc
      (1 : ℝ) ≤ 2 * (R * ‖T‖) + 1 := by linarith
      _ ≤ Real.exp (2 * (R * ‖T‖)) := Real.add_one_le_exp _
  have hanalytic :
      AnalyticOnNhd ℂ (fredholmDet T)
        (Metric.closedBall (0 : ℂ) |R|) := by
    intro z _
    exact (universalFredholmDet_analyticOnNhd T) z (Set.mem_univ z)
  have hnonzero : fredholmDet T 0 ≠ 0 := by
    rw [fredholmDet_zero]
    exact one_ne_zero
  have houter :
      ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
        ‖fredholmDet T z‖ ≤ Real.exp (2 * (R * ‖T‖)) := by
    intro z hz
    have hzNorm : ‖z‖ = R := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hR]
        using hz
    simpa only [hzNorm] using
      (universalFredholm_norm_le_exp_two_traceNorm T z)
  have hJ :=
    AnalyticOnNhd.sum_divisor_le
      (c := (0 : ℂ)) (r := r) (R := R)
      (M := Real.exp (2 * (R * ‖T‖)))
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hanalytic hnonzero houter
  simpa only [abs_of_pos hr, fredholmDet_zero, norm_one,
    div_one, Real.log_exp] using hJ

/-- At the concrete outer-radius choice R=2r, Jensen's inequality
gives a completely explicit bound linear in the inner radius and the
trace norm: the universal Fredholm zero count is at most
(4/log 2) r ‖T‖, with exact analytic multiplicities. -/
theorem universalFredholm_Jensen_zero_count_double_radius
    (T : ProbabilisticTheory.TraceClass H)
    {r : ℝ} (hr : 0 < r) :
    ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) r) u
      ≤ (4 * r * ‖T‖) / Real.log 2 := by
  have hRadius : r < 2 * r := by linarith
  have hbound :=
    universalFredholm_Jensen_zero_count_linear_traceNorm_bound T hr hRadius
  have hratio : (2 * r) / r = (2 : ℝ) := by
    field_simp [ne_of_gt hr]
  rw [hratio] at hbound
  convert hbound using 1 <;> ring

#print axioms Manuscript14Priority3.FredholmLinearJensenGrowth.universalFredholm_norm_le_exp_two_traceNorm
#print axioms Manuscript14Priority3.FredholmLinearJensenGrowth.universalFredholm_Jensen_zero_count_linear_traceNorm_bound
#print axioms Manuscript14Priority3.FredholmLinearJensenGrowth.universalFredholm_Jensen_zero_count_double_radius

end Manuscript14Priority3.FredholmLinearJensenGrowth
