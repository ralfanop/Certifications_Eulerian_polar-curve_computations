import Mathlib

/-!
Manuscript 16 v16.5, Theorem 14.5, equation (W1).
Source ZIP SHA-256:
4bde685f7a340e45c43f413aea973db50feea7ba30023f84aefa5de042499c0e

This is ONLY the scalar rational simplification of the difference of the
two Gibbs index means. It does NOT prove geometric-series summability,
stochastic dominance, the optimal-transport identification, or W_infinity.
-/

namespace Manuscript16.Section14.GibbsScalar

theorem mean_difference_rational (q : ℝ)
    (hq1 : q ≠ 1) (hq3 : q ≠ 3) :
    2 * (q * (3 / (1 - q) - 1 / (3 - q)) - q / (1 - q)) =
      4 * q / (1 - q) - 2 * q / (3 - q) := by
  have h1 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have h3 : 3 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq3)
  field_simp
  <;> ring

end Manuscript16.Section14.GibbsScalar
