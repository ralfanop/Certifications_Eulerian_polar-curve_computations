import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialIntegrability

/-!
# V007 — genuine integral / finite moment matrix for all real polynomials

For any two real polynomials p,q and the actual ultraspherical
Beta-pushforward probability measure, their product integral is
exactly the full finite double sum of moments, with coefficients
taken over the genuine polynomial supports.

This is an analytic identity of actual Bochner integrals.
An additional theorem must replace p by the polynomial operator's
finite monomial action to obtain the full differential Green form.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Product with an ordinary monomial: actual ultraspherical
integral equals the complete coefficient/moment contraction. -/
theorem sturmPolynomial_eval_mul_monomial_integral
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) (m : ℕ) :
    (∫ u : ℝ, p.eval u * u ^ m ∂(measure lam)) =
      ∑ n ∈ p.support, p.coeff n * sturmMoment lam (n + m) := by
  classical
  have heval (u : ℝ) :
      p.eval u * u ^ m =
        ∑ n ∈ p.support, p.coeff n * u ^ (n + m) := by
    rw [Polynomial.eval_eq_sum]
    simp only [Polynomial.sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [pow_add]
    ring
  calc
    (∫ u : ℝ, p.eval u * u ^ m ∂(measure lam)) =
        ∫ u : ℝ, ∑ n ∈ p.support, p.coeff n * u ^ (n + m)
          ∂(measure lam) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact heval u
    _ = ∑ n ∈ p.support,
          (∫ u : ℝ, p.coeff n * u ^ (n + m) ∂(measure lam)) := by
      rw [integral_finset_sum]
      intro n hn
      exact (sturmMoment_monomial_integrable lam hlam (n + m)).const_mul
        (p.coeff n)
    _ = ∑ n ∈ p.support, p.coeff n * sturmMoment lam (n + m) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul]
      rfl

/-- The true ultraspherical integral of a product of arbitrary real
polynomials is the complete finite double moment matrix. -/
theorem sturmPolynomial_eval_product_integral
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    (∫ u : ℝ, p.eval u * q.eval u ∂(measure lam)) =
      ∑ n ∈ p.support, ∑ m ∈ q.support,
        p.coeff n * q.coeff m * sturmMoment lam (n + m) := by
  classical
  have heval (u : ℝ) :
      p.eval u * q.eval u =
        ∑ m ∈ q.support, q.coeff m * (p.eval u * u ^ m) := by
    conv_lhs => rhs; rw [Polynomial.eval_eq_sum]
    simp only [Polynomial.sum, mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  calc
    (∫ u : ℝ, p.eval u * q.eval u ∂(measure lam)) =
        ∫ u : ℝ, ∑ m ∈ q.support, q.coeff m * (p.eval u * u ^ m)
          ∂(measure lam) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact heval u
    _ = ∑ m ∈ q.support,
        q.coeff m * (∫ u : ℝ, p.eval u * u ^ m ∂(measure lam)) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [integral_const_mul]
      · intro m hm
        have hprod :
          Integrable (fun u : ℝ => p.eval u * (X ^ m : ℝ[X]).eval u)
            (measure lam) :=
          sturmPolynomial_eval_product_integrable lam hlam p (X ^ m)
        simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
          hprod.const_mul (q.coeff m)
    _ = ∑ n ∈ p.support, ∑ m ∈ q.support,
          p.coeff n * q.coeff m * sturmMoment lam (n + m) := by
      simp_rw [sturmPolynomial_eval_mul_monomial_integral lam hlam p]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_eval_mul_monomial_integral
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_eval_product_integral

end GegenbauerFock.Ultraspherical
