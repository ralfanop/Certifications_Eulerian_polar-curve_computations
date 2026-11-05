import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialLinear
import GegenbauerFock.UltrasphericalSturmLiouvilleFullGreenIntegral

/-!
# V007 — actual real Hilbert L² Green identity on the polynomial core

This transfers the fully certified genuine Bochner-integral Green
identity to the actual real Hilbert-space inner product of L²(νλ).
The polynomial vectors were already certified to evaluate almost
everywhere to the original polynomial on the Beta-pushforward law.

This is symmetry on the polynomial VECTOR domain only. Well-defined
descent of the differential expression to the image, density, closure,
and essential self-adjointness are separate steps.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- The true real L² inner product of polynomial vectors is the
genuine integral of the real polynomial product. -/
theorem sturmRealPolynomialLp_inner_eq_integral
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    inner ℝ (sturmRealPolynomialLp lam hlam p)
      (sturmRealPolynomialLp lam hlam q) =
      ∫ u : ℝ, p.eval u * q.eval u ∂(measure lam) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [sturmRealPolynomialLp_ae_eval lam hlam p,
     sturmRealPolynomialLp_ae_eval lam hlam q]
    with u hp hq
  rw [hp, hq]
  simp only [RCLike.inner_apply']
  simp

/-- The full Green symmetry is now a genuine Hilbert inner-product
identity for polynomial L² vectors of the actual ultraspherical law. -/
theorem sturmRealPolynomialLp_green_inner_symm
    (lam : ℝ) (hlam : 0 < lam) (p q : ℝ[X]) :
    inner ℝ
        (sturmRealPolynomialLp lam hlam (sturmPolynomial lam p))
        (sturmRealPolynomialLp lam hlam q) =
      inner ℝ
        (sturmRealPolynomialLp lam hlam p)
        (sturmRealPolynomialLp lam hlam (sturmPolynomial lam q)) := by
  rw [sturmRealPolynomialLp_inner_eq_integral lam hlam
        (sturmPolynomial lam p) q,
      sturmRealPolynomialLp_inner_eq_integral lam hlam
        p (sturmPolynomial lam q)]
  exact sturmPolynomial_green_integral_symmetric lam hlam p q

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_inner_eq_integral
#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomialLp_green_inner_symm

end GegenbauerFock.Ultraspherical
