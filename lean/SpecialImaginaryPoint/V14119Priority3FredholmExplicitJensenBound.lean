import SpecialImaginaryPoint.V14119Priority3UniversalFredholmSpectralVariation
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Priority 3 — an explicit Jensen zero-count bound in the true Fredholm trace norm

The ACTUAL universal infinite-dimensional CFC Schatten-S₁ Hilbert-
compression-limit Fredholm determinant f_T(z)=det_F(I+zT), for an arbitrary
complex trace-class Hilbert operator T, satisfies f_T(0)=1 and is entire.

The previously certified universal spectral perturbation estimate gives
a dimension-free bound valid at all complex spectral shifts:
  ‖f_T(z)‖ ≤ 1 + ‖z‖‖T‖ exp(‖z‖‖T‖).

Applying Mathlib's general Jensen zero-count inequality yields an
operator-theoretic explicit bound, for 0 < r < R:
  total analytic multiplicity inside |z|≤r
    ≤ log(1 + R‖T‖ exp(R‖T‖)) / log(R/r).

This bound requires no mysterious a priori outer-circle constant M.
It uses ONLY the genuine CFC-S₁ trace norm of T and two positive radii.
The classical Jensen theorem itself is not claimed as a new theorem.
No normality, positivity, selfadjointness or spectral enumeration
is assumed.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmExplicitJensenBound

open Filter Topology Set Metric
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmSpectralVariation
open Manuscript14Priority3.MeromorphicFredholmReciprocal

/-- Global dimension-independent upper growth bound of the true
Hilbert-compression-limit Fredholm determinant in its trace norm. -/
theorem universalFredholm_norm_le_one_add_trace_exponential
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet T z‖ ≤
      1 + (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
  have h := universalFredholm_spectral_origin_norm_le T z
  calc
    ‖fredholmDet T z‖ =
        ‖(fredholmDet T z - 1) + (1 : ℂ)‖ := by
      congr 1
      ring
    _ ≤ ‖fredholmDet T z - 1‖ + ‖(1 : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) + 1 := by
      simpa only [norm_one] using add_le_add_right h 1
    _ = 1 + (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
      ring

/-- Explicit Jensen bound for the entire genuine universal Fredholm
zero divisor, with no external outer-circle modulus parameter:
the bound is expressed ONLY in the trace norm and positive radii. -/
theorem universalFredholm_Jensen_explicit_traceNorm_zero_count
    (T : ProbabilisticTheory.TraceClass H)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) r) u
      ≤ Real.log (1 + (R * ‖T‖) * Real.exp (R * ‖T‖)) /
          Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  let M : ℝ := 1 + (R * ‖T‖) * Real.exp (R * ‖T‖)
  have hM : 1 ≤ M := by
    dsimp [M]
    have hterm : 0 ≤ (R * ‖T‖) * Real.exp (R * ‖T‖) :=
      mul_nonneg (mul_nonneg hR.le (norm_nonneg T))
        (Real.exp_pos _).le
    linarith
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
        ‖fredholmDet T z‖ ≤ M := by
    intro z hz
    have hznorm : ‖z‖ = R := by
      simpa only [Metric.mem_sphere, dist_zero_right, abs_of_pos hR] using hz
    simpa only [M, hznorm] using
      (universalFredholm_norm_le_one_add_trace_exponential T z)
  have hJensen :=
    hanalytic.sum_divisor_le (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM hnonzero houter
  simpa only [abs_of_pos hr, fredholmDet_zero, norm_one, div_one, M]
    using hJensen

#print axioms Manuscript14Priority3.FredholmExplicitJensenBound.universalFredholm_norm_le_one_add_trace_exponential
#print axioms Manuscript14Priority3.FredholmExplicitJensenBound.universalFredholm_Jensen_explicit_traceNorm_zero_count

end Manuscript14Priority3.FredholmExplicitJensenBound
