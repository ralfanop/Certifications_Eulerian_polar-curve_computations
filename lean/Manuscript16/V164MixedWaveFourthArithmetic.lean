/- Manuscript 16 v16.4, Section 13: exact scalar algebra for the mixed
   nonresonant Maxwell/Dirac fourth-Schatten calculation.
   NOTE: none of these declarations identifies an operator trace or
   proves interchange of infinite spectral sums. -/
import Mathlib

namespace Manuscript16

/-- Deck-even temporal frequencies m = ell + 2*k give the exact
    nonresonant wave eigenvalue factorisation. -/
theorem mixedWave_evenMode_factor (ell k : ℤ) :
    ell ^ 2 - (ell + 2 * k) ^ 2 = -4 * k * (ell + k) := by
  ring

/-- The single nearest temporal mode m = ell+2 used in the
    necessary direction of the sharp Schatten threshold. -/
theorem mixedWave_upperNearestMode (ell : ℤ) :
    ell ^ 2 - (ell + 2) ^ 2 = -4 * (ell + 1) := by
  ring

/-- The quadratic cancellation after reindexing the two positive
    quadrant sums; the diagonal correction is a separate step. -/
theorem mixedWave_pairQuadratics (a b : ℝ) :
    ((a + b) ^ 2 - 1) + ((a - b) ^ 2 - 1) =
      2 * (a ^ 2 + b ^ 2 - 1) := by
  ring

/-- Algebraic substitution of Euler's even-zeta values.
    This is a scalar identity, not a certification of the spectral sum. -/
theorem mixedWave_zetaClosed_algebra (x : ℝ) :
    (4 * (x ^ 2 / 6) * (x ^ 4 / 90) -
       2 * (x ^ 4 / 90) ^ 2 + x ^ 8 / 9450) / 128 =
      x ^ 6 / 17280 - x ^ 8 / 907200 := by
  ring

/-- Algebraic addition of the spatial Dirac fourth-power expression. -/
theorem mixedWave_DiracClosed_algebra (x : ℝ) :
    x ^ 2 - x ^ 4 / 12 +
      (4 * (x ^ 2 / 6) * (x ^ 4 / 90) -
       2 * (x ^ 4 / 90) ^ 2 + x ^ 8 / 9450) / 128 =
      x ^ 2 - x ^ 4 / 12 + x ^ 6 / 17280 - x ^ 8 / 907200 := by
  ring

#print axioms Manuscript16.mixedWave_evenMode_factor
#print axioms Manuscript16.mixedWave_upperNearestMode
#print axioms Manuscript16.mixedWave_pairQuadratics
#print axioms Manuscript16.mixedWave_zetaClosed_algebra
#print axioms Manuscript16.mixedWave_DiracClosed_algebra

end Manuscript16
