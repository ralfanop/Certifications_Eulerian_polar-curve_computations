import GegenbauerFock.UltrasphericalSturmLiouvilleMomentIntegrability
import GegenbauerFock.UltrasphericalSturmLiouvilleLinearMap

/-!
# V007 — genuine integrability of real-polynomial Gegenbauer pairings

An ordinary real polynomial, its Sturm differential expression, and
their finite products are genuine L¹ functions of the concrete
Beta-pushforward ultraspherical probability law.

This prepares the transition from symmetric finite coefficient Green
matrices to actual weighted Lebesgue/Bochner integral identities.
No self-adjointness or unbounded operator domain is claimed here.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Ordinary real-polynomial evaluation is integrable for the actual
ultraspherical probability measure at every positive λ. -/
theorem sturmPolynomial_eval_integrable
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    Integrable (fun u : ℝ => p.eval u) (measure lam) := by
  classical
  have heval :
      (fun u : ℝ => p.eval u) =
        (fun u : ℝ => ∑ n ∈ p.support, p.coeff n * u ^ n) := by
    funext u
    simp only [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [heval]
  apply integrable_finset_sum
  intro n hn
  exact (sturmMoment_monomial_integrable lam hlam n).const_mul (p.coeff n)

/-- Both polynomial factors are evaluated in the genuine measure,
not in a formal moment space. -/
theorem sturmPolynomial_eval_product_integrable
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    Integrable (fun u : ℝ => p.eval u * q.eval u) (measure lam) := by
  have h :
      (fun u : ℝ => p.eval u * q.eval u) =
        (fun u : ℝ => (p * q).eval u) := by
    funext u
    simp
  rw [h]
  exact sturmPolynomial_eval_integrable lam hlam (p * q)

/-- The actual polynomial Gegenbauer differential expression has
integrable weighted products with any second polynomial. -/
theorem sturmPolynomial_operator_product_integrable
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    Integrable (fun u : ℝ =>
      (sturmPolynomial lam p).eval u * q.eval u) (measure lam) :=
  sturmPolynomial_eval_product_integrable lam hlam
    (sturmPolynomial lam p) q

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_eval_integrable
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_eval_product_integrable
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_operator_product_integrable

end GegenbauerFock.Ultraspherical
