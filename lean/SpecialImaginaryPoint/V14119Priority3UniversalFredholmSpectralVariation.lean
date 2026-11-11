import SpecialImaginaryPoint.V14119Priority3UniversalFredholmNonzeroDisk
import SpecialImaginaryPoint.V14119Priority3SpectralEquicontinuity

/-!
# Priority 3 — genuine universal Fredholm spectral-parameter perturbation bound

The true CFC Schatten-S₁ Hilbert-compression-limit determinant
f_T(z)=det_F(I+zT) of ANY complex trace-class Hilbert operator T
obeys a SHARP finite-compression spectral difference bound in the
limit, uniformly with respect to the compression dimensions:

  ‖f_T(z)-f_T(w)‖ ≤ ‖z-w‖ ‖T‖ exp((‖w‖+‖z-w‖) ‖T‖).

The second theorem specializes at the exact normalization f_T(0)=1.
These estimates need neither normality nor selfadjointness, and
make no extra assumption on finite nuclear representation costs.
-/

noncomputable section

namespace Manuscript14Priority3.UniversalFredholmSpectralVariation

open Filter Topology Set
open scoped InnerProductSpace Ring
open Manuscript14Priority3.TraceClassModel
open Manuscript14Priority3.UniversalFredholmExistence
open Manuscript14Priority3.SpectralEquicontinuity

/-- Spectral-parameter perturbation inequality for the ACTUAL
universal infinite-dimensional CFC-S₁ Fredholm determinant. -/
theorem universalFredholm_spectral_diff_norm_le
    (T : ProbabilisticTheory.TraceClass H) (z w : ℂ) :
    ‖fredholmDet T z - fredholmDet T w‖ ≤
      (‖z - w‖ * ‖T‖) *
        Real.exp ((‖w‖ + ‖z - w‖) * ‖T‖) := by
  have ht :
      Tendsto (fun N : ℕ =>
        finiteDeterminant N T z - finiteDeterminant N T w) atTop
        (𝓝 (fredholmDet T z - fredholmDet T w)) :=
    (finiteDeterminant_tendsto_fredholmDet T z).sub
      (finiteDeterminant_tendsto_fredholmDet T w)
  exact le_of_tendsto ht.norm <|
    Filter.Eventually.of_forall
      (fun N => finiteDeterminant_spectral_diff_norm_le N T z w)

/-- Normalization-centered explicit global spectral bound on
the TRUE universal CFC-S₁ Hilbert Fredholm determinant. -/
theorem universalFredholm_spectral_origin_norm_le
    (T : ProbabilisticTheory.TraceClass H) (z : ℂ) :
    ‖fredholmDet T z - 1‖ ≤
      (‖z‖ * ‖T‖) * Real.exp (‖z‖ * ‖T‖) := by
  simpa only [fredholmDet_zero, sub_zero, norm_zero, zero_add]
    using universalFredholm_spectral_diff_norm_le T z 0

#print axioms Manuscript14Priority3.UniversalFredholmSpectralVariation.universalFredholm_spectral_diff_norm_le
#print axioms Manuscript14Priority3.UniversalFredholmSpectralVariation.universalFredholm_spectral_origin_norm_le

end Manuscript14Priority3.UniversalFredholmSpectralVariation
