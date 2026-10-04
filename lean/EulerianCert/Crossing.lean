/-
# Remark 3.16 of the V478 manuscript: the crossing order

Lemma 3.15 of the manuscript proves, by Laplace's method applied to the Fourier inversion of Eq. (78),
`c_n = √(π(n+1)/216) · (1 + 15/(4(n+1)) + O(n⁻²))` (Eq. (81)), so the crossing `c_n = π`
(`α_n = ϑ_E`) moves from `n + 1 ≈ 216π` to `n + 1 ≈ 216π − 15/2`.

This file certifies the two numerical facts quoted with it:
* `crossing_bracket`: `670 < 216π − 15/2 < 672`, i.e. the corrected estimate lies strictly between
  the orders `n + 1 = 670` and `n + 1 = 672` bracketed by Eq. (82) (`EulerianCert.Bracket`);
* `one_term_outside`: `672 < 216π`, i.e. the one-term estimate falls outside that bracket.

The asymptotic expansion itself is analysis (Laplace's method) and is not formalised here;
`numerics/lemma315_asymptotic.py` checks it against the exact values of `c_n` for odd `n ≤ 1001`.
-/
import Mathlib.Analysis.Real.Pi.Bounds

namespace EulerianCert.Crossing

open Real

/-- Remark 3.16: `670 < 216π − 15/2 < 672`. -/
theorem crossing_bracket : (670 : ℝ) < 216 * π - 15 / 2 ∧ 216 * π - 15 / 2 < 672 := by
  constructor
  · linarith [pi_gt_d2]
  · linarith [pi_lt_d4]

/-- Remark 3.16: the one-term estimate `216π` exceeds `672`. -/
theorem one_term_outside : (672 : ℝ) < 216 * π := by
  linarith [pi_gt_d2]

end EulerianCert.Crossing
