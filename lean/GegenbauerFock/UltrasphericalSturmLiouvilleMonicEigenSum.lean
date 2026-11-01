import GegenbauerFock.UltrasphericalSturmLiouvilleMonicEigenCoefficients
import GegenbauerFock.UltrasphericalSturmLiouvilleLinearMap

/-!
# V007 — uniform monomial Sturm action and monic-sum linearity

Every polynomial monomial, including degrees zero and one, has
the same diagonal-plus-lowering Sturm action. This avoids a spurious
separate boundary term when shifting the finite Gegenbauer sum.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- The triangular Sturm action on EVERY natural monomial degree.
For degrees zero and one the lowering coefficient vanishes. -/
theorem sturmPolynomial_X_pow_diagonal_lower
    (lam : ℝ) (j : ℕ) :
    sturmPolynomial lam (X ^ j) =
      C ((j : ℝ) * ((j : ℝ) - 1)) * X ^ (j-2) +
        C (sturmEigenvalue lam j) * X ^ j := by
  rcases j with _ | j
  · simp [sturmPolynomial, sturmEigenvalue]
  rcases j with _ | n
  · simp [sturmPolynomial_X, sturmEigenvalue, sub_eq_add_neg]
    ring
  · have hj : n+1+1 = n+2 := by omega
    rw [hj, sturmPolynomial_X_pow_succ_succ]
    have hlo : n+2-2=n := by omega
    rw [hlo]
    simp only [sturmEigenvalue]
    push_cast
    simp only [map_neg, neg_mul]
    ring

/-- The differential operator acts termwise on the actual finite
monic Gegenbauer candidate; no infinite interchange occurs. -/
theorem sturmPolynomial_monicCandidate_as_sum
    (lam : ℝ) (n : ℕ) :
    sturmPolynomial lam (sturmMonicEigenCandidate lam n) =
      ∑ k ∈ Finset.range (n/2+1),
        C (sturmMonicCoeff lam n k) *
          sturmPolynomial lam (X ^ (n-2*k)) := by
  change (sturmPolynomialLinear lam)
    (∑ k ∈ Finset.range (n/2+1),
      C (sturmMonicCoeff lam n k) * X ^ (n-2*k)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change sturmPolynomial lam
    (C (sturmMonicCoeff lam n k) * X ^ (n-2*k)) =
    C (sturmMonicCoeff lam n k) *
      sturmPolynomial lam (X ^ (n-2*k))
  simpa only [smul_eq_C_mul] using
    (sturmPolynomial_smul lam (sturmMonicCoeff lam n k)
      (X ^ (n-2*k)))

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_X_pow_diagonal_lower
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_monicCandidate_as_sum

end GegenbauerFock.Ultraspherical
