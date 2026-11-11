import SpecialImaginaryPoint.V14119Priority3AdmissibleContourRadii
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact

/-!
# Priority 3 — positive uniform Fredholm determinant gap on zero-free circles

For any arbitrary complex Schatten-S₁ Hilbert trace-class operator T,
the actual universal Fredholm determinant f_T(z)=det_F(I+zT) is entire.
A radius r outside the countable exceptional set of genuine spectral
zero radii gives a compact circle containing no determinant zeros.

Compactness and continuity upgrade pointwise nonvanishing to a SINGLE
strictly positive real lower bound δ for |f_T(z)| simultaneously at
every point on the complex circle |z|=r.

This is the uniform denominator bound needed to control meromorphic
reciprocals and logarithmic derivatives in later contour integrals.
No argument-principle identity is asserted here.
-/

noncomputable section

namespace Manuscript14Priority3.UniformFredholmContourGap

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.UniversalFredholmEntire
open Manuscript14Priority3.AdmissibleContourRadii

/-- On EVERY admissible spectral circle there is a UNIFORM strictly
positive modulus bound for the actual infinite-dimensional
CFC-S₁ Fredholm determinant, with no normality hypothesis. -/
theorem universalFredholm_exists_positive_uniform_circle_gap
    (T : ProbabilisticTheory.TraceClass H) (r : ℝ)
    (hr : r ∈ (universalFredholmZeroRadiusSet T)ᶜ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, ‖z‖ = r → δ ≤ ‖fredholmDet T z‖ := by
  have hcompact : IsCompact (Metric.sphere (0 : ℂ) r) :=
    isCompact_sphere _ _
  have hcontinuous :
      ContinuousOn (fun z : ℂ => ‖fredholmDet T z‖)
        (Metric.sphere (0 : ℂ) r) :=
    ((universal_fredholmDet_entire T).continuous.norm).continuousOn
  have hpositive :
      ∀ z ∈ Metric.sphere (0 : ℂ) r,
        (0 : ℝ) < ‖fredholmDet T z‖ := by
    intro z hz
    apply norm_pos_iff.mpr
    apply universalFredholm_nonzero_on_admissible_circle T r hr z
    simpa only [Metric.mem_sphere, dist_zero_right] using hz
  obtain ⟨δ, hδpos, hδ⟩ :=
    hcompact.exists_forall_le' hcontinuous hpositive
  refine ⟨δ, hδpos, ?_⟩
  intro z hz
  apply hδ z
  simpa only [Metric.mem_sphere, dist_zero_right] using hz

#print axioms Manuscript14Priority3.UniformFredholmContourGap.universalFredholm_exists_positive_uniform_circle_gap

end Manuscript14Priority3.UniformFredholmContourGap
