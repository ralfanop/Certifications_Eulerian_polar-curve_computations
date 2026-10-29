import GegenbauerFock.UltrasphericalSturmLiouvilleLinearMap

/-!
# V007 — exact ordering of the ultraspherical polynomial eigenvalue candidates

The triangular real-polynomial Gegenbauer operator has proposed
diagonal values d_n = -n(n+2λ). These are nonpositive, strictly
decreasing, and pairwise distinct for every λ>0.

This is a purely scalar theorem: the existence of a complete Hilbert
basis of genuine Gegenbauer eigenpolynomials remains an additional
operator-theoretic obligation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- The exact leading diagonal scalar of the n-th polynomial degree
in the genuine Gegenbauer Sturm expression. -/
def sturmEigenvalue (lam : ℝ) (n : ℕ) : ℝ :=
  -(n : ℝ) * ((n : ℝ) + 2 * lam)

@[simp] theorem sturmEigenvalue_zero (lam : ℝ) :
    sturmEigenvalue lam 0 = 0 := by
  simp [sturmEigenvalue]

theorem sturmEigenvalue_nonpos (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) : sturmEigenvalue lam n ≤ 0 := by
  unfold sturmEigenvalue
  have h1 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : 0 ≤ (n : ℝ) + 2 * lam := by positivity
  exact neg_nonpos.mpr (mul_nonneg h1 h2)

theorem sturmEigenvalue_strictAnti (lam : ℝ) (hlam : 0 < lam) :
    StrictAnti (sturmEigenvalue lam) := by
  intro n m hnm
  have hn : (n : ℝ) < (m : ℝ) := Nat.cast_lt.mpr hnm
  have hm : 0 < (m : ℝ) := lt_of_le_of_lt (Nat.cast_nonneg n) hn
  have hpos :
      0 < ((m : ℝ) - (n : ℝ)) *
          ((m : ℝ) + (n : ℝ) + 2 * lam) :=
    mul_pos (sub_pos.mpr hn) (by positivity)
  have hdiff :
      sturmEigenvalue lam n - sturmEigenvalue lam m =
        ((m : ℝ) - (n : ℝ)) *
          ((m : ℝ) + (n : ℝ) + 2 * lam) := by
    unfold sturmEigenvalue
    ring
  rw [← hdiff] at hpos
  exact sub_pos.mp hpos

/-- Distinct nonnegative polynomial degrees have distinct diagonal
Gegenbauer eigenvalue candidates at λ>0. -/
theorem sturmEigenvalue_injective (lam : ℝ) (hlam : 0 < lam) :
    Function.Injective (sturmEigenvalue lam) :=
  (sturmEigenvalue_strictAnti lam hlam).injective

#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_zero
#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_nonpos
#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_strictAnti
#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_injective

end GegenbauerFock.Ultraspherical
