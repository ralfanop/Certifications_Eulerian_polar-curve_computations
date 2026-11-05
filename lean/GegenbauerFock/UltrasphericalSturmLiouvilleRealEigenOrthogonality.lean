import GegenbauerFock.UltrasphericalSturmLiouvilleRealL2Green
import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# V007: Genuine L² orthogonality of distinct ultraspherical eigenpolynomials
This theorem assumes two exact polynomial eigenequations. It does not
assume that eigenvectors exist for every degree or form a Hilbert basis.
-/
noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

theorem sturmRealPolynomial_eigen_orthogonal
    (lam : ℝ) (hlam : 0 < lam)
    (p q : ℝ[X]) (n m : ℕ)
    (hp : sturmPolynomial lam p = sturmEigenvalue lam n • p)
    (hq : sturmPolynomial lam q = sturmEigenvalue lam m • q)
    (hnm : n ≠ m) :
    inner ℝ (sturmRealPolynomialLp lam hlam p)
      (sturmRealPolynomialLp lam hlam q) = 0 := by
  have hne : sturmEigenvalue lam n ≠ sturmEigenvalue lam m := by
    intro h
    exact hnm ((sturmEigenvalue_injective lam hlam) h)
  have hgreen := sturmRealPolynomialLp_green_inner_symm lam hlam p q
  rw [hp, hq,
    sturmRealPolynomialLp_smul lam hlam (sturmEigenvalue lam n) p,
    sturmRealPolynomialLp_smul lam hlam (sturmEigenvalue lam m) q]
      at hgreen
  simp only [real_inner_smul_left, real_inner_smul_right] at hgreen
  have hzero :
      (sturmEigenvalue lam n - sturmEigenvalue lam m) *
          inner ℝ (sturmRealPolynomialLp lam hlam p)
            (sturmRealPolynomialLp lam hlam q) = 0 := by
    calc
      _ = sturmEigenvalue lam n *
          inner ℝ (sturmRealPolynomialLp lam hlam p)
            (sturmRealPolynomialLp lam hlam q) -
          sturmEigenvalue lam m *
          inner ℝ (sturmRealPolynomialLp lam hlam p)
            (sturmRealPolynomialLp lam hlam q) := by ring
      _ = 0 := sub_eq_zero.mpr hgreen
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hne)

#print axioms GegenbauerFock.Ultraspherical.sturmRealPolynomial_eigen_orthogonal

end GegenbauerFock.Ultraspherical
