import GegenbauerFock.UltrasphericalSturmLiouvilleMonomialIntegralBridge
import GegenbauerFock.UltrasphericalSturmLiouvilleAllMonomialPairs

/-!
# V007 — genuine integral monomial Green matrix, all degrees

For any natural monomial degrees n,m and λ>0, the actual weighted
integral of the Gegenbauer polynomial differential expression applied
to X^n equals the exact scalar monomial moment matrix entry.
The zero/linear modes are handled separately, avoiding negative
integer powers or an artificial assumption that n≥2.

This is an identity of genuine integrals against the concrete
Beta-pushforward ultraspherical measure, not a postulated bilinear form.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Exact all-degree integral realization of each Green matrix entry
for the genuine ultraspherical probability measure. -/
theorem sturmPolynomial_monomial_integral_pair
    (lam : ℝ) (hlam : 0 < lam) (n m : ℕ) :
    (∫ u : ℝ,
        (sturmPolynomial lam (X ^ n)).eval u * u ^ m
          ∂(measure lam)) =
      sturmMonomialMomentPair lam n m := by
  rcases n with _ | n
  · simp [sturmPolynomial, sturmMonomialMomentPair]
  rcases n with _ | k
  · have hpoint :
        (fun u : ℝ =>
          (sturmPolynomial lam (X ^ 1)).eval u * u ^ m) =
        (fun u : ℝ => -(2 * lam + 1) * u ^ (m + 1)) := by
      funext u
      rw [pow_one, sturmPolynomial_X]
      simp only [Polynomial.eval_neg, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      rw [pow_succ]
      ring
    rw [hpoint, integral_const_mul]
    change -(2 * lam + 1) * sturmMoment lam (m + 1) =
      sturmMonomialMomentPair lam 1 m
    unfold sturmMonomialMomentPair
    simp only [Nat.cast_one, one_sub_self, mul_zero, zero_mul,
      zero_sub, one_mul]
    have hidx : 1 + m = m + 1 := by omega
    rw [hidx]
    ring
  · have h := sturmPolynomial_high_monomial_integral lam hlam k m
    have hindex1 : (k + 2) + m - 2 = k + m := by omega
    have hindex2 : (k + 2) + m = k + m + 2 := by omega
    change
      (∫ u : ℝ,
        (sturmPolynomial lam (X ^ (k + 2))).eval u * u ^ m
          ∂(measure lam)) =
        sturmMonomialMomentPair lam (k + 2) m
    rw [h]
    unfold sturmMonomialMomentPair
    rw [hindex1, hindex2]
    push_cast
    ring

/-- The true measure integral Green coefficients are symmetric for
every monomial pair, without degree exclusions. -/
theorem sturmPolynomial_monomial_integral_symm
    (lam : ℝ) (hlam : 0 < lam) (n m : ℕ) :
    (∫ u : ℝ,
        (sturmPolynomial lam (X ^ n)).eval u * u ^ m
          ∂(measure lam)) =
    (∫ u : ℝ,
        (sturmPolynomial lam (X ^ m)).eval u * u ^ n
          ∂(measure lam)) := by
  rw [sturmPolynomial_monomial_integral_pair lam hlam n m,
      sturmPolynomial_monomial_integral_pair lam hlam m n]
  exact sturmMonomialMomentPair_symmetric lam hlam n m

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_monomial_integral_pair
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_monomial_integral_symm

end GegenbauerFock.Ultraspherical
