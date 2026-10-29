import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialExpansion
import GegenbauerFock.UltrasphericalSturmLiouvilleAllMonomialIntegrals
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialMatrixForm
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialIntegrability

/-!
# V007 — complete real-polynomial Green identity in the actual measure

For all real polynomials p, q and all λ>0, this module connects
the genuine integral of the actual polynomial differential operator
against the true ultraspherical probability measure to the
previously certified finite monomial moment Green matrix.

The integral Green symmetry is then an equality between real
Bochner integrals, not merely a symmetry of symbolic matrices.
This remains the polynomial core, NOT a claim of essential
self-adjointness of any unbounded Hilbert-space operator.
-/

noncomputable section
open MeasureTheory
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Real polynomial action paired with an arbitrary monomial,
computed by the genuine actual ultraspherical Bochner integral. -/
theorem sturmPolynomial_operator_monomial_integral
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) (m : ℕ) :
    (∫ u : ℝ,
       (sturmPolynomial lam p).eval u * u ^ m ∂(measure lam)) =
      ∑ n ∈ p.support,
        p.coeff n * sturmMonomialMomentPair lam n m := by
  classical
  have hpoint (u : ℝ) :
      (sturmPolynomial lam p).eval u * u ^ m =
        ∑ n ∈ p.support,
          p.coeff n *
            ((sturmPolynomial lam (X ^ n)).eval u * u ^ m) := by
    rw [sturmPolynomial_apply_sum_monomials lam p]
    rw [Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  calc
    (∫ u : ℝ,
       (sturmPolynomial lam p).eval u * u ^ m ∂(measure lam)) =
        ∫ u : ℝ,
          ∑ n ∈ p.support,
            p.coeff n *
              ((sturmPolynomial lam (X ^ n)).eval u * u ^ m)
          ∂(measure lam) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact hpoint u
    _ = ∑ n ∈ p.support,
          (∫ u : ℝ,
            p.coeff n *
              ((sturmPolynomial lam (X ^ n)).eval u * u ^ m)
            ∂(measure lam)) := by
      rw [integral_finset_sum]
      intro n hn
      have hp :
          Integrable (fun u : ℝ =>
            (sturmPolynomial lam (X ^ n)).eval u * (X ^ m : ℝ[X]).eval u)
              (measure lam) :=
        sturmPolynomial_eval_product_integrable lam hlam
          (sturmPolynomial lam (X ^ n)) (X ^ m)
      simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
        hp.const_mul (p.coeff n)
    _ = ∑ n ∈ p.support,
          p.coeff n * sturmMonomialMomentPair lam n m := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_const_mul,
        sturmPolynomial_monomial_integral_pair lam hlam n m]

/-- The integral of (Lλ p)q for arbitrary real polynomials is exactly
the full finite Green coefficient matrix, for the genuine measure. -/
theorem sturmPolynomial_operator_integral_eq_matrix
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    (∫ u : ℝ,
      (sturmPolynomial lam p).eval u * q.eval u ∂(measure lam)) =
      sturmPolynomialGreenMatrixForm lam p q := by
  classical
  have hpoint (u : ℝ) :
      (sturmPolynomial lam p).eval u * q.eval u =
        ∑ m ∈ q.support,
          q.coeff m *
            ((sturmPolynomial lam p).eval u * u ^ m) := by
    conv_lhs => rhs; rw [Polynomial.eval_eq_sum]
    simp only [Polynomial.sum, mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  calc
    (∫ u : ℝ,
      (sturmPolynomial lam p).eval u * q.eval u ∂(measure lam)) =
        ∫ u : ℝ, ∑ m ∈ q.support,
          q.coeff m *
            ((sturmPolynomial lam p).eval u * u ^ m)
          ∂(measure lam) := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact hpoint u
    _ = ∑ m ∈ q.support,
        q.coeff m *
          (∫ u : ℝ,
            (sturmPolynomial lam p).eval u * u ^ m ∂(measure lam)) := by
      rw [integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro m hm
        rw [integral_const_mul]
      · intro m hm
        have hp :
            Integrable (fun u : ℝ =>
              (sturmPolynomial lam p).eval u * (X ^ m : ℝ[X]).eval u)
                (measure lam) :=
          sturmPolynomial_eval_product_integrable lam hlam
            (sturmPolynomial lam p) (X ^ m)
        simpa only [Polynomial.eval_pow, Polynomial.eval_X] using
          hp.const_mul (q.coeff m)
    _ = sturmPolynomialGreenMatrixForm lam p q := by
      simp_rw [sturmPolynomial_operator_monomial_integral lam hlam p]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      unfold sturmPolynomialGreenMatrixForm
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- Green symmetry is an equality of actual real integrals for all
polynomials in the concrete ultraspherical beta-pushforward measure. -/
theorem sturmPolynomial_green_integral_symmetric
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    (∫ u : ℝ,
      (sturmPolynomial lam p).eval u * q.eval u ∂(measure lam)) =
    (∫ u : ℝ,
      p.eval u * (sturmPolynomial lam q).eval u ∂(measure lam)) := by
  calc
    (∫ u : ℝ,
      (sturmPolynomial lam p).eval u * q.eval u ∂(measure lam)) =
        sturmPolynomialGreenMatrixForm lam p q :=
      sturmPolynomial_operator_integral_eq_matrix lam hlam p q
    _ = sturmPolynomialGreenMatrixForm lam q p :=
      sturmPolynomialGreenMatrixForm_symm lam hlam p q
    _ = (∫ u : ℝ,
          (sturmPolynomial lam q).eval u * p.eval u ∂(measure lam)) :=
      (sturmPolynomial_operator_integral_eq_matrix lam hlam q p).symm
    _ = (∫ u : ℝ,
          p.eval u * (sturmPolynomial lam q).eval u ∂(measure lam)) := by
      apply integral_congr_ae
      filter_upwards [] with u
      ring

#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_operator_monomial_integral
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_operator_integral_eq_matrix
#print axioms GegenbauerFock.Ultraspherical.sturmPolynomial_green_integral_symmetric

end GegenbauerFock.Ultraspherical
