import SpecialImaginaryPoint.V14119Priority3UniformFredholmContourGap

/-!
# Priority 3 — stable zero-free Fredholm spectral contours under trace-norm perturbations

For any complex CFC Schatten-S₁ trace-class Hilbert operator T and
every admissible circle |z|=r not containing zeros of its genuine
universal infinite-dimensional Fredholm determinant f_T(z),
there exists a UNIFORM strictly positive modulus gap δ>0.

Any trace-class perturbation R for which the already certified
global trace-norm determinant perturbation bound falls strictly
below δ along this circle preserves NONVANISHING AT EVERY POINT
on the entire circle. The condition is quantitative and uniform
in the angular parameter, not an assertion about the zero count
INSIDE the circle or the classical Rouché theorem.

No positivity, normality, diagonalizability, selfadjointness or
eigenvalue enumeration assumptions are used.
-/

noncomputable section

namespace Manuscript14Priority3.RobustFredholmSpectralCircles

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.AdmissibleContourRadii
open Manuscript14Priority3.UniformFredholmContourGap

/-- The true universal CFC-S₁ Fredholm determinant remains nonzero
on an ENTIRE admissible complex spectral circle under an explicit
trace-class perturbation controlled by the uniform determinant gap. -/
theorem universalFredholm_zeroFree_circle_stable_of_traceNorm_bound
    (T : ProbabilisticTheory.TraceClass H) (r : ℝ)
    (hr : r ∈ (universalFredholmZeroRadiusSet T)ᶜ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ (R : ProbabilisticTheory.TraceClass H),
        (r * ‖R‖) * Real.exp (r * (‖T‖ + ‖R‖)) < δ →
          ∀ z : ℂ, ‖z‖ = r → fredholmDet (T + R) z ≠ 0) := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    universalFredholm_exists_positive_uniform_circle_gap T r hr
  refine ⟨δ, hδpos, ?_⟩
  intro R hsmall z hz hzero
  have hpert := fredholmDet_add_traceNorm_bound T R z
  have hlower : ‖fredholmDet T z‖ ≤
      (‖z‖ * ‖R‖) * Real.exp (‖z‖ * (‖T‖ + ‖R‖)) := by
    simpa only [hzero, zero_sub, norm_neg] using hpert
  rw [hz] at hlower
  have hcontr : δ ≤ (r * ‖R‖) * Real.exp (r * (‖T‖ + ‖R‖)) :=
    (hδ z hz).trans hlower
  exact (not_lt_of_ge hcontr) hsmall

#print axioms Manuscript14Priority3.RobustFredholmSpectralCircles.universalFredholm_zeroFree_circle_stable_of_traceNorm_bound

end Manuscript14Priority3.RobustFredholmSpectralCircles
