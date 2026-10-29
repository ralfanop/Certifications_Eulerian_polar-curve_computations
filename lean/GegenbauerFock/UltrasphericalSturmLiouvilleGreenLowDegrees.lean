import GegenbauerFock.UltrasphericalSturmLiouvilleActualMoments

/-!
# V007 — missing low-degree Green pair identities

These are the remaining degree 0 and 1 pairings against every
monomial of degree at least 2, for the genuine Beta-pushforward
ultraspherical law. Together with the high-high Green coefficient
theorem, they provide the scalar monomial-level algebraic identities
needed for full polynomial-core symmetry.

They do not assert realization or self-adjointness on the full L² space.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

/-- The Gegenbauer operator's coefficient for L(X^(a+2)) has zero
moment against the constant polynomial; L(1)=0. -/
theorem sturmMoment_green_with_constant
    (lam : ℝ) (hlam : 0 < lam) (a : ℕ) :
    (((a + 2 : ℕ) : ℝ) * ((a + 1 : ℕ) : ℝ)) *
        sturmMoment lam a -
      (((a + 2 : ℕ) : ℝ) * (((a + 2 : ℕ) : ℝ) + 2 * lam)) *
        sturmMoment lam (a + 2) = 0 := by
  have hrec := sturmMoment_two_step lam hlam a
  push_cast at hrec ⊢
  linear_combination (-((a : ℝ) + 2)) * hrec

/-- The Gegenbauer differential action on X has the eigenvalue
-(2λ+1). This verifies its Green pairing with every X^(a+2). -/
theorem sturmMoment_green_with_linear
    (lam : ℝ) (hlam : 0 < lam) (a : ℕ) :
    (((a + 2 : ℕ) : ℝ) * ((a + 1 : ℕ) : ℝ)) *
        sturmMoment lam (a + 1) -
      (((a + 2 : ℕ) : ℝ) * (((a + 2 : ℕ) : ℝ) + 2 * lam)) *
        sturmMoment lam (a + 3) =
      -(2 * lam + 1) * sturmMoment lam (a + 3) := by
  have hrec := sturmMoment_two_step lam hlam (a + 1)
  push_cast at hrec ⊢
  linear_combination (-((a : ℝ) + 1)) * hrec

#print axioms GegenbauerFock.Ultraspherical.sturmMoment_green_with_constant
#print axioms GegenbauerFock.Ultraspherical.sturmMoment_green_with_linear

end GegenbauerFock.Ultraspherical
