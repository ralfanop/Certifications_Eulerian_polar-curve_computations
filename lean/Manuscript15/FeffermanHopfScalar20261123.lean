import Mathlib

/-!
Manuscript 15, 23 November 2026, Hopf-basic spectral reduction.
Source ZIP SHA-256: 156727733a941b4126c133957692a9e451b0de1e8f736abf3b0fe85dba73545f.

Arithmetic of the spherical degree and periodic scalar eigenvalues.
This does not formalise the differential-geometric Hopf submersion or its
Laplacian intertwiner.
-/
namespace Manuscript15.Fefferman20261123

/-- The degree-2j sphere eigenvalue equals the base value 4j(j+1). -/
theorem doubled_degree_eigenvalue (j : ℕ) :
    (2 * j) * (2 * j + 2) = 4 * j * (j + 1) := by
  ring

/-- The even temporal frequency gives 4[j(j+1)-m²]. -/
theorem hopf_mode_eigenvalue_factor (j : ℕ) (m : ℤ) :
    4 * (j : ℤ) * ((j : ℤ) + 1) - (2 * m) ^ 2 =
      4 * ((j : ℤ) * ((j : ℤ) + 1) - m ^ 2) := by
  ring

/-- A positive j places j(j+1) strictly between two consecutive squares. -/
theorem between_consecutive_squares (j : ℕ) (hj : 0 < j) :
    j ^ 2 < j * (j + 1) ∧ j * (j + 1) < (j + 1) ^ 2 := by
  constructor <;> nlinarith

/-- A nonzero spatial degree cannot be a temporal square.
Negative integer frequencies are covered since their squares agree. -/
theorem no_positive_degree_square (j m : ℕ) (hj : 0 < j) :
    j * (j + 1) ≠ m ^ 2 := by
  intro heq
  rcases le_total m j with h | h
  · nlinarith
  · by_cases h' : m = j
    · subst m
      nlinarith
    · have hsucc : j + 1 ≤ m := by omega
      nlinarith

theorem zero_degree_only_zero_frequency (m : ℤ) (hm : m ^ 2 = 0) :
    m = 0 := by
  nlinarith

#print axioms Manuscript15.Fefferman20261123.doubled_degree_eigenvalue
#print axioms Manuscript15.Fefferman20261123.hopf_mode_eigenvalue_factor
#print axioms Manuscript15.Fefferman20261123.between_consecutive_squares
#print axioms Manuscript15.Fefferman20261123.no_positive_degree_square
#print axioms Manuscript15.Fefferman20261123.zero_degree_only_zero_frequency
end Manuscript15.Fefferman20261123
