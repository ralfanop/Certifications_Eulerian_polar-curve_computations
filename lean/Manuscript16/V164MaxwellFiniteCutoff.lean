/- Manuscript 16 v16.4, Proposition 13.
   Exact finite-cutoff arithmetic for the nonresonant Maxwell p=3
   nearest-mode obstruction. The analytic divergence and operator
   spectral identification are NOT established by these lemmas. -/
import Mathlib
import Manuscript16.V164MaxwellThirdShellLowerBound

namespace Manuscript16

/-- Exact positive difference between the nearest-mode third-power
    shell and the shifted harmonic comparison term. -/
theorem v164_maxwell_third_shell_exact_gap (x : ℝ) (hx : 0 < x + 1) :
    2 * (x ^ 2 - 1) / (4 * (x + 1)) ^ 3 -
      1 / (96 * (x + 1)) =
      (x - 2) / (48 * (x + 1) ^ 2) := by
  have h : x + 1 ≠ 0 := ne_of_gt hx
  field_simp
  <;> ring

/-- Finite cutoff comparison for any selection of spatial indices
    ell >= 2. This does not assert convergence or divergence. -/
theorem v164_maxwell_finite_cutoff_lower
    (s : Finset ℕ) (hs : ∀ ell ∈ s, 2 ≤ ell) :
    (∑ ell ∈ s, (1 : ℝ) / (96 * ((ell : ℝ) + 1))) ≤
      ∑ ell ∈ s, 2 * (((ell : ℝ) ^ 2) - 1) /
        ((4 * ((ell : ℝ) + 1)) ^ 3) := by
  apply Finset.sum_le_sum
  intro ell hmem
  exact v164_maxwell_third_shell_ge_harmonic ell (hs ell hmem)

/-- Explicit finite interval from 2 through N; a bridge to the
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
#print axioms Manuscript16.v164_maxwell_finite_cutoff_lower
#print axioms Manuscript16.v164_maxwell_interval_cutoff_lower

end Manuscript16
