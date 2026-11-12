import SpecialImaginaryPoint.V14119Priority3FredholmExplicitJensenBound

/-!
# Priority 3 — scale-invariant Jensen bounds for true CFC-S₁ Fredholm spectral zero counts

Starting from the rigorous, dimension-independent Jensen inequality
for the actual universal Hilbert-compression Fredholm determinant
f_T(z)=det_F(I+zT) of any (possibly nonnormal) Schatten-S₁ operator T,
we specialize the outer circle to a fixed dilation k>1 of the
inner radius r>0.

The resulting spectral zero count, with analytic multiplicities,
is bounded by a *fully explicit* trace-norm expression with
the constant denominator log(k). At k=2, this gives the standard
doubling-disk Jensen zero-count estimate with denominator log(2).

Theorems reuse Mathlib's classical Jensen inequality and the
previously kernel-certified true universal CFC-S₁ Fredholm bound.
No assertion of novelty for classical Jensen analysis is intended.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmJensenDilation

open Filter Topology Set Metric MeromorphicOn
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.FredholmExplicitJensenBound

/-- Any dilation factor k>1 gives an explicit count of actual
Fredholm determinant zeros, with analytic multiplicities, inside
the closed spectral disk of radius r, using only k,r and ‖T‖. -/
theorem universalFredholm_Jensen_dilated_traceNorm_zero_count
    (T : ProbabilisticTheory.TraceClass H)
    {r k : ℝ} (hr : 0 < r) (hk : 1 < k) :
    ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) r) u
      ≤ Real.log
          (1 + ((k * r) * ‖T‖) *
            Real.exp ((k * r) * ‖T‖)) / Real.log k := by
  have hrR : r < k * r := by
    have hpos : 0 < (k - 1) * r :=
      mul_pos (sub_pos.mpr hk) hr
    nlinarith
  have h :=
    universalFredholm_Jensen_explicit_traceNorm_zero_count T
      (r := r) (R := k * r) hr hrR
  have hratio : (k * r) / r = k := by
    field_simp [ne_of_gt hr]
  simpa only [hratio] using h

/-- At the doubling scale, genuine universal CFC trace-class Fredholm
zeros have an explicit analytic-multiplicity count bounded by
log(1 + 2r‖T‖exp(2r‖T‖)) / log 2. -/
theorem universalFredholm_Jensen_doubling_zero_count
    (T : ProbabilisticTheory.TraceClass H)
    {r : ℝ} (hr : 0 < r) :
    ∑ᶠ u, divisor (fredholmDet T) (Metric.closedBall (0 : ℂ) r) u
      ≤ Real.log
          (1 + ((2 * r) * ‖T‖) *
            Real.exp ((2 * r) * ‖T‖)) / Real.log 2 := by
  exact universalFredholm_Jensen_dilated_traceNorm_zero_count T
    (r := r) (k := 2) hr (by norm_num)

#print axioms Manuscript14Priority3.FredholmJensenDilation.universalFredholm_Jensen_dilated_traceNorm_zero_count
#print axioms Manuscript14Priority3.FredholmJensenDilation.universalFredholm_Jensen_doubling_zero_count

end Manuscript14Priority3.FredholmJensenDilation
