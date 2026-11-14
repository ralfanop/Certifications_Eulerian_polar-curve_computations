/-
Manuscript 16 v16.1 (14 November 2026).
This module certifies the scalar Dirac fourth-summand decomposition,
the CONVERGENCE of that actual multiplicity-weighted scalar series
(through the shifted real p-series criterion in pinned Mathlib),
and the finite resonance multiplicity polynomial.

The geometric spectrum, eigenbasis completeness, Schatten-ideal
identification, zeta evaluations, and analytic winding theorem are
NOT asserted or proved here.
-/
import Mathlib

noncomputable section

namespace Manuscript16

/-- The n-th scalar summand of the absolute fourth-power trace, using
the spinor multiplicity for each sign. -/
def diracFourthShell (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) / (((n : ℝ) + 3 / 2) ^ 4)

/-- Shifted reciprocal series, with a positive real shift 3/2. -/
def shiftedDiracReciprocal (s : ℝ) (n : ℕ) : ℝ :=
  1 / |(n : ℝ) + (3 / 2 : ℝ)| ^ s

/-- This is an actual identity for every spectral index, not only
a formal substitution after evaluation of zeta-values. -/
theorem diracFourthShell_decomposition (n : ℕ) :
    diracFourthShell n =
      2 * shiftedDiracReciprocal 2 n -
        (1 / 2 : ℝ) * shiftedDiracReciprocal 4 n := by
  unfold diracFourthShell shiftedDiracReciprocal
  have hpos : 0 < (n : ℝ) + 3 / 2 := by positivity
  rw [abs_of_pos hpos]
  simp only [Real.rpow_ofNat]
  have hne : (n : ℝ) + 3 / 2 ≠ 0 := ne_of_gt hpos
  field_simp [hne]
  <;> ring

/-- Genuine summability of the shifted reciprocal p-series for s>1.
This uses Mathlib's analytic p-series theorem. -/
theorem shiftedDiracReciprocal_summable (s : ℝ) (hs : 1 < s) :
    Summable (shiftedDiracReciprocal s) := by
  exact (Real.summable_one_div_nat_add_rpow (3 / 2) s).2 hs

/-- Genuine convergence of the scalar Dirac fourth trace series,
conditional on the spectral multiplicity formula being the right one.
This is more than a finite algebraic simplification. -/
theorem diracFourthShell_summable : Summable diracFourthShell := by
  have h2 : Summable (shiftedDiracReciprocal 2) :=
    shiftedDiracReciprocal_summable 2 (by norm_num)
  have h4 : Summable (shiftedDiracReciprocal 4) :=
    shiftedDiracReciprocal_summable 4 (by norm_num)
  have hsum : Summable (fun n : ℕ =>
      2 * shiftedDiracReciprocal 2 n -
        (1 / 2 : ℝ) * shiftedDiracReciprocal 4 n) :=
    (h2.mul_left 2).sub (h4.mul_left (1 / 2))
  have hf : diracFourthShell =
      (fun n : ℕ => 2 * shiftedDiracReciprocal 2 n -
        (1 / 2 : ℝ) * shiftedDiracReciprocal 4 n) := by
    funext n
    exact diracFourthShell_decomposition n
  rw [hf]
  exact hsum

theorem diracFourthShell_nonneg (n : ℕ) :
    0 ≤ diracFourthShell n := by
  unfold diracFourthShell
  positivity

/-- An exact finite-sum formula for N consecutive angular degrees
ell=2,...,N+1, expressed by ell=j+2 with j in range N. -/
theorem transverse_winding_range_polynomial (N : ℕ) :
    (∑ j ∈ Finset.range N, (2 : ℚ) * (((j : ℚ) + 2) ^ 2 - 1)) =
      (N : ℚ) * ((N : ℚ) + 1) * (2 * (N : ℚ) + 7) / 3 := by
  induction N with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

#print axioms Manuscript16.diracFourthShell_decomposition
#print axioms Manuscript16.shiftedDiracReciprocal_summable
#print axioms Manuscript16.diracFourthShell_summable
#print axioms Manuscript16.diracFourthShell_nonneg
#print axioms Manuscript16.transverse_winding_range_polynomial


/-- Exact finite-level identity, useful before identifying the operator trace. -/
theorem diracFourthShell_partial_sum (N : ℕ) :
    (∑ n ∈ Finset.range N, diracFourthShell n) =
      2 * (∑ n ∈ Finset.range N, shiftedDiracReciprocal 2 n) -
      (1 / 2 : ℝ) * (∑ n ∈ Finset.range N, shiftedDiracReciprocal 4 n) := by
  simp_rw [diracFourthShell_decomposition]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The finite fourth-trace approximants strictly increase with cutoff. -/
theorem diracFourthShell_partial_sum_strict (N : ℕ) :
    (∑ n ∈ Finset.range N, diracFourthShell n) <
      (∑ n ∈ Finset.range (N + 1), diracFourthShell n) := by
  rw [Finset.sum_range_succ]
  have hpos : 0 < diracFourthShell N := by
    unfold diracFourthShell
    positivity
  linarith

#print axioms Manuscript16.diracFourthShell_partial_sum
#print axioms Manuscript16.diracFourthShell_partial_sum_strict

end Manuscript16
