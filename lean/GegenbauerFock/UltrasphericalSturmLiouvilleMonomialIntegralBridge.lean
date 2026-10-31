import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialIntegrability

/-!
# V007 — actual integral of the Gegenbauer action on a high monomial

The polynomial action, evaluated on the real support, is integrated
against another monomial in the *actual* Beta-pushforward ultraspherical
probability measure. The resulting exact integral equals the scalar
moment matrix coefficient, without postulating Green symmetry.

This is a first genuine analytic bridge from finite monomial coefficients
to the weighted L¹ integration used by the eventual L² operator.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Genuine integral of the differential expression applied to
X^(k+2), paired with X^m, expressed in true measure moments. -/
theorem sturmPolynomial_high_monomial_integral
    (lam : ℝ) (hlam : 0 < lam) (k m : ℕ) :
    (∫ u : ℝ,
       (sturmPolynomial lam (X ^ (k + 2))).eval u * u ^ m
       ∂(measure lam)) =
      (((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)) *
          sturmMoment lam (k + m) -
        (((k + 2 : ℕ) : ℝ) *
          (((k + 2 : ℕ) : ℝ) + 2 * lam)) *
          sturmMoment lam (k + m + 2) := by
  let a : ℝ := ((k + 2 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ)
  let b : ℝ := ((k + 2 : ℕ) : ℝ) *
    (((k + 2 : ℕ) : ℝ) + 2 * lam)
  have hpoint :
      (fun u : ℝ =>
          (sturmPolynomial lam (X ^ (k + 2))).eval u * u ^ m) =
        (fun u : ℝ => a * u ^ (k + m) - b * u ^ (k + m + 2)) := by
    funext u
    rw [sturmPolynomial_X_pow_succ_succ lam k]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    change (a * u ^ k - b * u ^ (k + 2)) * u ^ m =
      a * u ^ (k + m) - b * u ^ (k + m + 2)
    rw [show k + m + 2 = (k + 2) + m by omega]
    simp only [pow_add]
    ring
  rw [hpoint]
  rw [integral_sub
    ((sturmMoment_monomial_integrable lam hlam (k + m)).const_mul a)
    ((sturmMoment_monomial_integrable lam hlam (k + m + 2)).const_mul b)]
  rw [integral_const_mul, integral_const_mul]
  rfl

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_high_monomial_integral

end GegenbauerFock.Ultraspherical
