/-
Manuscript 16, v16.1 (14 November 2026).
Lean 4 arithmetic audit of the fourth trace identity, transverse winding
polynomial, and Schur coupling threshold.

Scope: only algebraic steps are formalised here; no spectral theorem,
zeta evaluation, Schatten membership, unbounded-domain result or
Fredholm determinant is thereby certified.
-/
import Mathlib

namespace Manuscript16

/-- The final polynomial identity in the winding-count proof,
conditional on the sum-of-squares formula. -/
theorem winding_polynomial_arithmetic (n : ℝ) :
    2 * (n * (n + 1) * (2 * n + 1) / 6 - n) =
      n * (n - 1) * (2 * n + 5) / 3 := by
  ring

/-- Hurwitz-zeta reduction after inserting the classical special values. -/
theorem dirac_fourth_trace_arithmetic (pi : ℝ) :
    2 * (pi ^ 2 / 2 - 4) - (1 / 2 : ℝ) * (pi ^ 4 / 6 - 16) =
      pi ^ 2 - pi ^ 4 / 12 := by
  ring

/-- Coupled fourth-trace polynomial, after substituting ζ(6), ζ(8). -/
theorem coupled_fourth_trace_arithmetic (pi : ℝ) :
    (pi ^ 2 - pi ^ 4 / 12) +
        2 * (pi ^ 6 / 945 - pi ^ 8 / 9450) =
      pi ^ 2 - pi ^ 4 / 12 + 2 * pi ^ 6 / 945 - pi ^ 8 / 4725 := by
  ring

/-- Positivity of the Neumann-series margin in the Schur bound. -/
theorem schur_neumann_margin_pos (a d x : ℝ)
    (ha : 0 < a) (hd : 0 < d) (hx : x < a * d) :
    0 < 1 - x / (a * d) := by
  have had : 0 < a * d := mul_pos ha hd
  have hfrac : x / (a * d) < 1 := (div_lt_one had).2 hx
  linarith

/-- Algebraic rational simplification of the Schur norm bound. -/
theorem schur_bound_rational_identity (a d x : ℝ)
    (ha : a ≠ 0) (hd : d ≠ 0) (hgap : a * d - x ≠ 0) :
    (1 / a) / (1 - x / (a * d)) = d / (a * d - x) := by
  field_simp [ha, hd, hgap]
  <;> ring

/-- Unperturbed Maxwell-Dirac diagonal-gap product. -/
theorem unperturbed_coupling_gap : (4 : ℝ) * (3 / 2) = 6 := by
  norm_num

#print axioms Manuscript16.winding_polynomial_arithmetic
#print axioms Manuscript16.dirac_fourth_trace_arithmetic
#print axioms Manuscript16.coupled_fourth_trace_arithmetic
#print axioms Manuscript16.schur_neumann_margin_pos
#print axioms Manuscript16.schur_bound_rational_identity
#print axioms Manuscript16.unperturbed_coupling_gap

end Manuscript16
