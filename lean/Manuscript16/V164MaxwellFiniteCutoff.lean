/- Manuscript 16 v16.4, Proposition 13.
   Exact finite-cutoff arithmetic for the nonresonant Maxwell p=3
   nearest-mode obstruction. The analytic divergence and operator
   spectral identification are NOT established by these lemmas.

   Self-contained Mathlib import: do not rely on a hand-written .olean
   that is not registered in Lake's LEAN_PATH. -/
import Mathlib

namespace Manuscript16

/-- Exact difference between the nearest-mode third-power shell
    and the shifted harmonic comparison term. -/
theorem v164_maxwell_third_shell_exact_gap (x : ℝ) (hx : 0 < x + 1) :
    2 * (x ^ 2 - 1) / (4 * (x + 1)) ^ 3 -
      1 / (96 * (x + 1)) =
      (x - 2) / (48 * (x + 1) ^ 2) := by
  have h : x + 1 ≠ 0 := ne_of_gt hx
  field_simp
  <;> ring

/-- Pointwise inequality proved from the exact gap, without a
    non-Lake-registered import of the preceding PR #310. -/
theorem v164_maxwell_third_shell_gap_nonneg (x : ℝ) (hx : 2 ≤ x) :
    1 / (96 * (x + 1)) ≤
      2 * (x ^ 2 - 1) / (4 * (x + 1)) ^ 3 := by
  have hpos : 0 < x + 1 := by linarith
  have hnum : 0 ≤ x - 2 := by linarith
  have hden : 0 ≤ 48 * (x + 1) ^ 2 := by positivity
  have hfrac : 0 ≤ (x - 2) / (48 * (x + 1) ^ 2) :=
    div_nonneg hnum hden
  have hgap := v164_maxwell_third_shell_exact_gap x hpos
  linarith

/-- Comparison on an arbitrary finite set of Maxwell spatial modes. -/
theorem v164_maxwell_finite_cutoff_lower
    (s : Finset ℕ) (hs : ∀ ell ∈ s, 2 ≤ ell) :
    (∑ ell ∈ s, (1 : ℝ) / (96 * ((ell : ℝ) + 1))) ≤
      ∑ ell ∈ s, 2 * (((ell : ℝ) ^ 2) - 1) /
        ((4 * ((ell : ℝ) + 1)) ^ 3) := by
  apply Finset.sum_le_sum
  intro ell hmem
  have hell : (2 : ℝ) ≤ (ell : ℝ) := by exact_mod_cast hs ell hmem
  exact v164_maxwell_third_shell_gap_nonneg (ell : ℝ) hell

/-- Explicit finite interval from 2 through N; bridge to the
    separate analytic nonsummability obligation. -/
theorem v164_maxwell_interval_cutoff_lower (N : ℕ) :
    (∑ ell ∈ Finset.Icc 2 N,
       (1 : ℝ) / (96 * ((ell : ℝ) + 1))) ≤
      ∑ ell ∈ Finset.Icc 2 N,
        2 * (((ell : ℝ) ^ 2) - 1) /
          ((4 * ((ell : ℝ) + 1)) ^ 3) := by
  apply v164_maxwell_finite_cutoff_lower
  intro ell hmem
  exact (Finset.mem_Icc.mp hmem).1

#print axioms Manuscript16.v164_maxwell_third_shell_exact_gap
#print axioms Manuscript16.v164_maxwell_third_shell_gap_nonneg
#print axioms Manuscript16.v164_maxwell_finite_cutoff_lower
#print axioms Manuscript16.v164_maxwell_interval_cutoff_lower

end Manuscript16
