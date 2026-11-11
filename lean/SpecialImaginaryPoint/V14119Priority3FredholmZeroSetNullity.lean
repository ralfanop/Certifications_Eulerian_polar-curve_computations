import SpecialImaginaryPoint.V14119Priority3GenericFredholmSpectralParameters
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Priority 3 — nullity of the genuine Fredholm spectral zero set

For every genuine CFC Schatten-S₁ Hilbert operator T, the spectral
zero set of its universal compression-limit Fredholm determinant is
countable, hence null for EVERY complex Borel measure whose singletons
have zero measure. In particular it has zero planar Lebesgue measure.

This is an operatorial corollary of the countability of genuine universal
Fredholm zeros; no diagonal, positivity or normality hypothesis is used.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmZeroSetNullity

open MeasureTheory Set
open Manuscript14Priority3.LocallyFiniteFredholmZeroSet
open Manuscript14Priority3.CountableUniversalSpectralZeros

/-- The spectral zero set is null for any measure with null singletons,
including arbitrary diffuse Borel measures on ℂ. -/
theorem universalFredholmZeroSet_measure_zero
    (T : ProbabilisticTheory.TraceClass H) (μ : Measure ℂ)
    [NullSingletonClass μ] :
    μ (universalFredholmZeroSet T) = 0 := by
  exact (universalFredholmZeroSet_countable T).measure_zero μ

/-- The genuine universal Fredholm determinant has a spectral zero set
of zero two-dimensional Lebesgue measure on the complex plane. -/
theorem universalFredholmZeroSet_volume_zero
    (T : ProbabilisticTheory.TraceClass H) :
    (volume : Measure ℂ) (universalFredholmZeroSet T) = 0 := by
  exact universalFredholmZeroSet_measure_zero T volume

#print axioms Manuscript14Priority3.FredholmZeroSetNullity.universalFredholmZeroSet_measure_zero
#print axioms Manuscript14Priority3.FredholmZeroSetNullity.universalFredholmZeroSet_volume_zero

end Manuscript14Priority3.FredholmZeroSetNullity
