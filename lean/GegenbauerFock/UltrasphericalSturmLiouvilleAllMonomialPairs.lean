import GegenbauerFock.UltrasphericalSturmLiouvilleActualMoments

/-!
# V007 — universal Green matrix identity for actual ultraspherical moments

For all natural degrees n,m, including degrees 0 and 1, the action
of the Gegenbauer differential expression on X^n paired with X^m
has the scalar moment expression below. The zero coefficient of the
potentially negative-degree term makes the formula valid at n=0,1.

This module establishes symmetry of the explicit monomial moment
matrix using ONLY the exact two-step recurrence of the genuine
Beta-pushforward measure (and its odd first moment).

The statement is algebraic in its moment integrals. It is NOT yet
an equality between L² pairings of an unbounded differential operator.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

/-- The true moment pairing of the formal Gegenbauer differential
expression on the n-th monomial against the m-th monomial.
The truncated natural exponent is harmless for n=0 or n=1 because
its coefficient vanishes exactly in those cases. -/
noncomputable def sturmMonomialMomentPair
    (lam : ℝ) (n m : ℕ) : ℝ :=
  (n : ℝ) * ((n : ℝ) - 1) * sturmMoment lam (n + m - 2) -
    (n : ℝ) * ((n : ℝ) + 2 * lam) * sturmMoment lam (n + m)

/-- The exact first moment vanishes for the genuine symmetric
Beta-pushforward probability law. -/
theorem sturmMoment_one_eq_zero (lam : ℝ) (hlam : 0 < lam) :
    sturmMoment lam 1 = 0 := by
  change oddMoment lam 0 = 0
  exact oddMoment_eq_zero lam hlam 0

/-- All real monomial Gegenbauer Green matrix entries are symmetric
for the actual ultraspherical measure, including low-degree modes. -/
theorem sturmMonomialMomentPair_symmetric
    (lam : ℝ) (hlam : 0 < lam) (n m : ℕ) :
    sturmMonomialMomentPair lam n m =
      sturmMonomialMomentPair lam m n := by
  unfold sturmMonomialMomentPair
  by_cases hsum : 2 ≤ n + m
  · have hidx : n + m - 2 + 2 = n + m := by omega
    have hreal :
        ((n + m - 2 : ℕ) : ℝ) = (n : ℝ) + (m : ℝ) - 2 := by
      have hnat : n + m - 2 + 2 = n + m := hidx
      have hc : ((n + m - 2 : ℕ) : ℝ) + 2 =
          (n : ℝ) + (m : ℝ) := by
        exact_mod_cast hnat
      linarith
    have hrec := sturmMoment_two_step lam hlam (n + m - 2)
    rw [hidx] at hrec
    have hrec' :
        ((n : ℝ) + (m : ℝ) + 2 * lam) *
          sturmMoment lam (n + m) =
        ((n : ℝ) + (m : ℝ) - 1) *
          sturmMoment lam (n + m - 2) := by
      convert hrec using 1 <;> push_cast <;> (try rw [hreal]) <;> ring
    have hcomm : m + n = n + m := Nat.add_comm m n
    rw [hcomm]
    linear_combination ((m : ℝ) - (n : ℝ)) * hrec'
  · have hsmall :
        (n = 0 ∧ m = 0) ∨
        (n = 0 ∧ m = 1) ∨
        (n = 1 ∧ m = 0) := by omega
    rcases hsmall with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · ring
    · simp [sturmMoment_one_eq_zero lam hlam]
    · simp [sturmMoment_one_eq_zero lam hlam]

#print axioms GegenbauerFock.Ultraspherical.sturmMoment_one_eq_zero
#print axioms GegenbauerFock.Ultraspherical.sturmMonomialMomentPair_symmetric

end GegenbauerFock.Ultraspherical
