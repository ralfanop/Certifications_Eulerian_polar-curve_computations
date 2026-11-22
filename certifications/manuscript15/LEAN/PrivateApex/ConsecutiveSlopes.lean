import EulerianCert.EulerianFourier
import PrivateApex.FiniteComparisons
import Mathlib.Tactic

/-!
PRIVATE: Manuscript 15, Section 7.2 -- consecutive central slopes.

For `n = 2m ≥ 4` the Eulerian recurrence and the symmetry of the rows give
`E(2m+1,m) - E(2m+1,m-1) = (m+2) (E(2m,m-1) - E(2m,m-2))`, hence

  `t_n = 2 (n+1)² / ((n+2)(n+4)) · s_{n+1}`,   and   `t_n < 2 s_{n+1}` when `s_{n+1} > 0`.

Here `slopeQ n` (module `FiniteComparisons`) is the exact rational central slope:
`slopeQ (2m+1) = s_{2m+1}` and `slopeQ (2m) = t_{2m}`; both readings are proved below
(`slopeQ_odd`, `slopeQ_even`), so every statement is about the actual Eulerian numbers `E`.
-/
namespace PrivateApex
open EulerianCert.Bracket

theorem centralIndex_odd (m : ℕ) : centralIndex (2 * m + 1) = m := by
  unfold centralIndex; omega

theorem centralIndex_even {m : ℕ} (hm : 1 ≤ m) : centralIndex (2 * m) = m - 1 := by
  unfold centralIndex; omega

/-- For odd `n = 2m+1`, `slopeQ n` is the manuscript's `s_n = (n+1)[E(n,m) - E(n,m-1)]/n!`. -/
theorem slopeQ_odd (m : ℕ) :
    slopeQ (2 * m + 1) = ((2 * m + 1 : ℕ) + 1 : ℚ) *
      ((E (2 * m + 1) m : ℚ) - E (2 * m + 1) (m - 1)) / (2 * m + 1).factorial := by
  unfold slopeQ; rw [centralIndex_odd]

/-- For even `n = 2m`, `slopeQ n` is the manuscript's `t_n = (n+1)[E(n,m-1) - E(n,m-2)]/n!`. -/
theorem slopeQ_even {m : ℕ} (hm : 1 ≤ m) :
    slopeQ (2 * m) = ((2 * m : ℕ) + 1 : ℚ) *
      ((E (2 * m) (m - 1) : ℚ) - E (2 * m) (m - 2)) / (2 * m).factorial := by
  unfold slopeQ; rw [centralIndex_even hm, show m - 1 - 1 = m - 2 by omega]

/-- Central symmetry of an even row: `E(2m,m) = E(2m,m-1)`. -/
theorem E_even_central_symm {m : ℕ} (hm : 1 ≤ m) : E (2 * m) m = E (2 * m) (m - 1) := by
  have h := EulerianCert.EulerianFourier.eulerian_symmetry (n := 2 * m) (k := m + 1)
    (by omega) (by omega) (by omega)
  rw [show m + 1 - 1 = m by omega, show 2 * m - (m + 1) = m - 1 by omega] at h
  exact h

/-- The central difference of order `2m+1` is `m+2` times the central difference of order `2m`
(written additively, in `ℕ`). -/
theorem central_difference_add {m : ℕ} (hm : 2 ≤ m) :
    E (2 * m + 1) m + (m + 2) * E (2 * m) (m - 2) =
      E (2 * m + 1) (m - 1) + (m + 2) * E (2 * m) (m - 1) := by
  have h1 : E (2 * m + 1) m = (m + 1) * E (2 * m) m + (m + 1) * E (2 * m) (m - 1) := by
    have h := E_succ (m := 2 * m) (k := m) (by omega) (by omega)
    rw [show 2 * m + 1 - m = m + 1 by omega] at h
    exact h
  have h2 : E (2 * m + 1) (m - 1) = m * E (2 * m) (m - 1) + (m + 2) * E (2 * m) (m - 2) := by
    have h := E_succ (m := 2 * m) (k := m - 1) (by omega) (by omega)
    rw [show m - 1 + 1 = m by omega, show 2 * m + 1 - (m - 1) = m + 2 by omega,
      show m - 1 - 1 = m - 2 by omega] at h
    exact h
  rw [h1, h2, E_even_central_symm (by omega : 1 ≤ m)]
  ring

/-- The same identity for the integer differences. -/
theorem central_difference_int {m : ℕ} (hm : 2 ≤ m) :
    (E (2 * m + 1) m : ℤ) - E (2 * m + 1) (m - 1) =
      ((m : ℤ) + 2) * ((E (2 * m) (m - 1) : ℤ) - E (2 * m) (m - 2)) := by
  have h := congrArg (Nat.cast : ℕ → ℤ) (central_difference_add hm)
  push_cast at h
  linarith

/-- **Identity between consecutive central slopes**: for `n = 2m ≥ 4`,
`t_n = 2 (n+1)² / ((n+2)(n+4)) · s_{n+1}`. -/
theorem slopeQ_even_eq {m : ℕ} (hm : 2 ≤ m) :
    slopeQ (2 * m) = 2 * ((2 * m : ℕ) + 1 : ℚ) ^ 2 /
      ((((2 * m : ℕ) : ℚ) + 2) * (((2 * m : ℕ) : ℚ) + 4)) * slopeQ (2 * m + 1) := by
  have hd := congrArg (Nat.cast : ℕ → ℚ) (central_difference_add hm)
  push_cast at hd
  have hq : (E (2 * m + 1) m : ℚ) - E (2 * m + 1) (m - 1) =
      ((m : ℚ) + 2) * ((E (2 * m) (m - 1) : ℚ) - E (2 * m) (m - 2)) := by linarith
  rw [slopeQ_odd, slopeQ_even (by omega : 1 ≤ m), hq, Nat.factorial_succ]
  have hf : ((2 * m).factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The rational factor `2 (n+1)² / ((n+2)(n+4))` lies strictly between `0` and `2`. -/
theorem slope_factor_bounds (m : ℕ) :
    0 < 2 * ((2 * m : ℕ) + 1 : ℚ) ^ 2 / ((((2 * m : ℕ) : ℚ) + 2) * (((2 * m : ℕ) : ℚ) + 4)) ∧
    2 * ((2 * m : ℕ) + 1 : ℚ) ^ 2 / ((((2 * m : ℕ) : ℚ) + 2) * (((2 * m : ℕ) : ℚ) + 4)) < 2 := by
  have hm : (0 : ℚ) ≤ ((2 * m : ℕ) : ℚ) := by positivity
  constructor
  · positivity
  · rw [div_lt_iff₀ (by positivity)]
    nlinarith

/-- `t_n < 2 s_{n+1}` for `n = 2m ≥ 4`, as soon as `s_{n+1} > 0`. -/
theorem slopeQ_even_lt_two_mul {m : ℕ} (hm : 2 ≤ m) (hpos : 0 < slopeQ (2 * m + 1)) :
    slopeQ (2 * m) < 2 * slopeQ (2 * m + 1) := by
  rw [slopeQ_even_eq hm]
  exact mul_lt_mul_of_pos_right (slope_factor_bounds m).2 hpos

/-- `t_n > 0` for `n = 2m ≥ 4`, as soon as `s_{n+1} > 0`. -/
theorem slopeQ_even_pos {m : ℕ} (hm : 2 ≤ m) (hpos : 0 < slopeQ (2 * m + 1)) :
    0 < slopeQ (2 * m) := by
  rw [slopeQ_even_eq hm]
  exact mul_pos (slope_factor_bounds m).1 hpos

#print axioms central_difference_add
#print axioms central_difference_int
#print axioms slopeQ_even_eq
#print axioms slopeQ_even_lt_two_mul
#print axioms slopeQ_even_pos
end PrivateApex
