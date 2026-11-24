import Mathlib

/-!
Manuscript 15, "REFERENCES_REPAIRED_FINAL", Section Hopf-basic spectral reduction,
Eq. (hopf-fefferman-mode-spectrum) and Corollary hopf-basic-nonresonance.
Second-stage arithmetic formalization: frequencies in ℤ, not only ℕ.
The spherical-harmonic and Lorentzian-operator eigenfunction hypotheses
remain separate geometric/spectral obligations.
-/
namespace Manuscript15.FeffermanNullModes20261123

theorem integer_between_squares_nonresonance (j : ℕ) (m : ℤ)
    (hj : 0 < j) :
    (j : ℤ) * ((j : ℤ) + 1) ≠ m ^ 2 := by
  intro heq
  have hJ : (0 : ℤ) < (j : ℤ) := by exact_mod_cast hj
  have hlo : (j : ℤ) ^ 2 < (j : ℤ) * ((j : ℤ) + 1) := by nlinarith
  have hhi : (j : ℤ) * ((j : ℤ) + 1) < ((j : ℤ) + 1) ^ 2 := by nlinarith
  by_cases hmlo : m < -(j : ℤ)
  · have hbound : m ≤ -((j : ℤ) + 1) := by omega
    have hp : 0 ≤ (-(m + ((j : ℤ) + 1))) *
        (-(m - ((j : ℤ) + 1))) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  · by_cases hmhi : (j : ℤ) < m
    · have hbound : (j : ℤ) + 1 ≤ m := by omega
      have hp : 0 ≤ (m - ((j : ℤ) + 1)) *
          (m + ((j : ℤ) + 1)) :=
        mul_nonneg (by omega) (by omega)
      nlinarith
    · have hp : 0 ≤ ((j : ℤ) - m) * ((j : ℤ) + m) :=
        mul_nonneg (by omega) (by omega)
      nlinarith

/-- Exact arithmetic kernel classification for integer frequency m.
This is not yet a formal theorem about every smooth null solution. -/
theorem periodic_null_eigenvalue_iff (j : ℕ) (m : ℤ) :
    4 * ((j : ℤ) * ((j : ℤ) + 1) - m ^ 2) = 0 ↔
      j = 0 ∧ m = 0 := by
  constructor
  · intro h
    have heq : (j : ℤ) * ((j : ℤ) + 1) = m ^ 2 := by nlinarith [h]
    by_cases hj : j = 0
    · subst j
      simp only [Nat.cast_zero, zero_mul] at heq
      have hm : m = 0 := by nlinarith [sq_nonneg m]
      exact ⟨rfl, hm⟩
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj
      exact False.elim (integer_between_squares_nonresonance j m hjpos heq)
  · rintro ⟨rfl, rfl⟩
    norm_num

#print axioms Manuscript15.FeffermanNullModes20261123.integer_between_squares_nonresonance
#print axioms Manuscript15.FeffermanNullModes20261123.periodic_null_eigenvalue_iff
end Manuscript15.FeffermanNullModes20261123
