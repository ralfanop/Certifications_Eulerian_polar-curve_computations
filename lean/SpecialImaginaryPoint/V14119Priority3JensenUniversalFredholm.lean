import SpecialImaginaryPoint.V14119Priority3UniversalFredholmLogDerivative
import Mathlib.Analysis.Complex.JensenFormula

/-!
# Priority 3 — Jensen's formula and Jensen's zero-count inequality for the TRUE universal Fredholm determinant

For an arbitrary complex CFC Schatten-S₁ Hilbert trace-class operator T,
let f_T(z)=det_F(I+zT) denote the actual universal infinite-dimensional
Hilbert-compression-limit Fredholm determinant. Independently certified
operatorial theory proves that f_T is entire on the whole complex plane
and normalized by f_T(0)=1.

The general Mathlib theorem for Jensen's formula now applies to
this *genuine operatorial* determinant. The central normalization removes
the log|f_T(0)| term, leaving the finite-support zero divisor exactly.

Jensen's inequality gives a quantitative upper bound on the number
of zeros, counted with their true analytic multiplicity, on a smaller
closed disk in terms of an upper modulus bound on a larger circle.

We reuse the classical Jensen theorem; originality is NOT claimed for
Jensen's formula itself. No auxiliary scalar determinant, normality,
selfadjointness, spectral enumeration or trace-resolvent identity is used.
-/

noncomputable section

namespace Manuscript14Priority3.JensenUniversalFredholm

open Filter Topology Set Metric MeromorphicOn
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.MeromorphicFredholmReciprocal

/-- JENSEN'S FORMULA specialized to the ACTUAL universal CFC-S₁
Fredholm determinant. Exact normalization f_T(0)=1 removes the
central constant and the divisor counts genuine operatorial zeros. -/
theorem universalFredholm_Jensen_circleAverage
    (T : ProbabilisticTheory.TraceClass H) (R : ℝ) (hR : R ≠ 0) :
    Real.circleAverage (fun z : ℂ => Real.log ‖fredholmDet T z‖) 0 R =
      ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) |R|) u *
        Real.log (R * ‖u‖⁻¹) := by
  have hanalytic :
      AnalyticOnNhd ℂ (fredholmDet T)
        (Metric.closedBall (0 : ℂ) |R|) := by
    intro z _
    exact (universalFredholmDet_analyticOnNhd T) z (Set.mem_univ z)
  have hnonzero : fredholmDet T 0 ≠ 0 := by
    rw [fredholmDet_zero]
    exact one_ne_zero
  have hJensen :=
    AnalyticOnNhd.circleAverage_log_norm
      (c := (0 : ℂ)) (R := R) (f := fredholmDet T)
      hR hanalytic hnonzero
  simpa only [fredholmDet_zero, norm_one, Real.log_one, add_zero, zero_sub,
    norm_neg] using hJensen

/-- JENSEN'S ZERO-COUNT INEQUALITY, rigorously instantiated on the
true infinite-dimensional universal trace-class Fredholm determinant.
The divisor is the genuine analytic spectral zero divisor, without
an eigenvalue enumeration or normality assumptions. -/
theorem universalFredholm_Jensen_zero_count_bound
    (T : ProbabilisticTheory.TraceClass H)
    {r R M : ℝ} (hr : 0 < |r|) (hrR : |r| < |R|)
    (hM : 1 ≤ M)
    (houter : ∀ z ∈ Metric.sphere (0 : ℂ) |R|,
      ‖fredholmDet T z‖ ≤ M) :
    ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) |r|) u
      ≤ Real.log M / Real.log (R / r) := by
  have hanalytic :
      AnalyticOnNhd ℂ (fredholmDet T)
        (Metric.closedBall (0 : ℂ) |R|) := by
    intro z _
    exact (universalFredholmDet_analyticOnNhd T) z (Set.mem_univ z)
  have hnonzero : fredholmDet T 0 ≠ 0 := by
    rw [fredholmDet_zero]
    exact one_ne_zero
  have hJensen :=
    AnalyticOnNhd.sum_divisor_le
      (c := (0 : ℂ)) (r := r) (R := R) (M := M)
      hr hrR hM hanalytic hnonzero houter
  simpa only [fredholmDet_zero, norm_one, div_one] using hJensen

#print axioms Manuscript14Priority3.JensenUniversalFredholm.universalFredholm_Jensen_circleAverage
#print axioms Manuscript14Priority3.JensenUniversalFredholm.universalFredholm_Jensen_zero_count_bound

end Manuscript14Priority3.JensenUniversalFredholm
