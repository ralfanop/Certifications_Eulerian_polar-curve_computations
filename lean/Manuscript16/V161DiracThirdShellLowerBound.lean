/- Manuscript 16 v16.1. A pointwise necessary-side spectral comparison.
   This does NOT prove the full operator Schatten threshold. -/
import Mathlib

noncomputable section
namespace Manuscript16

/-- Multiplicity-weighted scalar third-power spectral shell. -/
def diracThirdShell (n : ℕ) : ℝ :=
  2 * ((n : ℝ) + 1) * ((n : ℝ) + 2) / (((n : ℝ) + 3 / 2) ^ 3)

/-- Lower bound by the harmonic shifted term, uniformly in n. -/
theorem diracThirdShell_ge_harmonic (n : ℕ) :
    1 / ((n : ℝ) + 3 / 2) ≤ diracThirdShell n := by
  unfold diracThirdShell
  have h : 0 < (n : ℝ) + 3 / 2 := by positivity
  have h2 : 0 < ((n : ℝ) + 3 / 2) ^ 2 := pow_pos h 2
  have h3 : 0 < ((n : ℝ) + 3 / 2) ^ 3 := pow_pos h 3
  apply (div_le_div_iff₀ h h3).2
  nlinarith [sq_nonneg (n : ℝ)]

#print axioms Manuscript16.diracThirdShell_ge_harmonic
end Manuscript16
