import SpecialImaginaryPoint.V14119Priority3UniversalFredholmSpectralVariation

/-!
# Priority 3 — quantitatively certified zero-exclusion region

For every complex CFC Schatten-S₁ trace-class Hilbert operator T, the
ACTUAL infinite-dimensional Hilbert-compression Fredholm determinant
f_T(z) = det_F(I + zT) obeys

  ‖f_T(z) - 1‖ ≤ (‖z‖ ‖T‖) exp(‖z‖ ‖T‖).

It follows rigorously and WITHOUT spectral enumeration that f_T(z)
does not vanish at any complex parameter satisfying

  (‖z‖ ‖T‖) exp(‖z‖ ‖T‖) < 1.

Conversely, each genuine zero must violate this strict inequality.
The statement is universal even for nonnormal/nonselfadjoint T.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmExplicitZeroExclusion

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.GenericFredholmSpectralParameters
open Manuscript14Priority3.UniversalFredholmSpectralVariation

/-- A genuinely quantitative, operator-independent-in-form
nonvanishing condition for the TRUE universal Fredholm determinant. -/
theorem universalFredholm_nonzero_of_exp_trace_threshold
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (h : (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) < 1) :
    fredholmDet T z ≠ 0 := by
  intro hz
  have hbound := universalFredholm_spectral_origin_norm_le T z
  have hcontradiction :
      (1 : ℝ) ≤ (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
    simpa [hz] using hbound
  exact (not_lt_of_ge hcontradiction) h

/-- EVERY genuine universal Fredholm spectral zero satisfies the
exact complementary quantitative necessary condition. -/
theorem universalFredholm_zero_exp_trace_lower_bound
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ)
    (hz : fredholmDet T z = 0) :
    (1 : ℝ) ≤ (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
  simpa [hz] using
    universalFredholm_spectral_origin_norm_le T z

/-- The explicit spectral-parameter region defined by the real
exponential threshold is contained in the OPEN DENSE domain of
nonvanishing of the actual universal CFC-S₁ Fredholm determinant. -/
theorem universalFredholm_exp_threshold_region_subset_nonzero
    (T : ProbabilisticTheory.TraceClass H) :
    {z : ℂ |
      (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) < 1} ⊆
        universalFredholmNonzeroSet T := by
  intro z hz
  exact (mem_universalFredholmNonzeroSet_iff T z).mpr
    (universalFredholm_nonzero_of_exp_trace_threshold T z hz)

#print axioms Manuscript14Priority3.UniversalFredholmExplicitZeroExclusion.universalFredholm_nonzero_of_exp_trace_threshold
#print axioms Manuscript14Priority3.UniversalFredholmExplicitZeroExclusion.universalFredholm_zero_exp_trace_lower_bound
#print axioms Manuscript14Priority3.UniversalFredholmExplicitZeroExclusion.universalFredholm_exp_threshold_region_subset_nonzero

end Manuscript14Priority3.UniversalFredholmExplicitZeroExclusion
