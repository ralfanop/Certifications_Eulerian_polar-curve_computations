import GegenbauerFock.TwoSidedGramNonclosedRange
import Mathlib.Analysis.Normed.Operator.Fredholm.Basic

/-!
# V007 — zero belongs to the Fredholm essential spectrum of both Grams

In the Fredholm definition of essential spectrum, a spectral value z
is essential when zI - T is not Fredholm. At z=0, that means the actual
bounded Hilbert operator T itself is not Fredholm (up to sign).

Mathlib's ContinuousLinearMap.IsFredholm has an explicit isClosed_range
field. The already kernel-certified nonclosed images of C†C and CC†
therefore provide the obstruction *without* appealing to a separate
unformalized singular Weyl criterion.

This module proves genuine non-Fredholmness at zero in the concrete
ultraspherical L² and full Gaussian-Fock coefficient Hilbert spaces.
It does not claim that Mathlib already has a built-in essential-spectrum
set API, or assert Fredholmness at other spectral parameters.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true source Gram C†C is not Fredholm: its range is not closed. -/
theorem sourceGram_zero_not_fredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ContinuousLinearMap.IsFredholm (gram lam alpha hlam ha) := by
  intro hfred
  exact (gram_range_not_closed lam alpha hlam ha) hfred.isClosed_range

/-- The true output Gram CC† is not Fredholm: its range is not closed. -/
theorem outputGram_zero_not_fredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ContinuousLinearMap.IsFredholm (outputGram lam alpha hlam ha) := by
  intro hfred
  exact (outputGram_range_not_closed lam alpha hlam ha) hfred.isClosed_range

/-- Non-Fredholmness at zero holds simultaneously for both Grams,
without identifying their different underlying Hilbert spaces. -/
theorem two_sided_gram_zero_not_fredholm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (¬ ContinuousLinearMap.IsFredholm (gram lam alpha hlam ha)) ∧
    (¬ ContinuousLinearMap.IsFredholm (outputGram lam alpha hlam ha)) :=
  ⟨sourceGram_zero_not_fredholm lam alpha hlam ha,
   outputGram_zero_not_fredholm lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_zero_not_fredholm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_not_fredholm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_zero_not_fredholm

end GegenbauerFock.GeneralUltrasphericalFock
