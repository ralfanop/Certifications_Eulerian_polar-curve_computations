import GegenbauerFock.UltrasphericalSturmLiouvilleMonicPointEigenvalues
import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# V007 — Fourier support of arbitrary closed Sturm Gegenbauer eigenvectors

The exact canonical closed operator diagonalization implies a stronger fact
than mere classification of point eigenvalues: if a genuine closed-domain
eigenvector belongs to eigenvalue -n(n+2λ), its Fourier-Gegenbauer
coefficients vanish at every degree except n. This applies to ALL
closed-domain eigenvectors, not only polynomial eigenmode candidates.

The proof uses the kernel-checked diagonalization and injectivity of the
strictly decreasing scalar Gegenbauer eigenvalue sequence.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The normalized Gegenbauer Fourier coordinates of an arbitrary
closed-domain eigenvector can be supported only at its eigenvalue's
unique polynomial degree. -/
theorem sturmRealClosed_eigenvector_single_degree_support
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : (sturmRealPartialOperator lam hlam).closure x =
      sturmEigenvalue lam n • (x : SturmH lam))
    (m : ℕ) (hm : m ≠ n) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      (x : SturmH lam) m = 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hdiag :=
    (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
      lam hlam).2 x m
  change (b.repr ((sturmRealPartialOperator lam hlam).closure x)) m =
    sturmEigenvalue lam m * (b.repr (x : SturmH lam)) m at hdiag
  rw [hx, map_smul] at hdiag
  change sturmEigenvalue lam n * (b.repr (x : SturmH lam)) m =
    sturmEigenvalue lam m * (b.repr (x : SturmH lam)) m at hdiag
  have hdiff :
      sturmEigenvalue lam n - sturmEigenvalue lam m ≠ 0 := by
    apply sub_ne_zero.mpr
    intro heq
    exact hm ((sturmEigenvalue_injective lam hlam heq).symm)
  have hmul :
      (sturmEigenvalue lam n - sturmEigenvalue lam m) *
        (b.repr (x : SturmH lam)) m = 0 := by
    calc
      _ = sturmEigenvalue lam n * (b.repr (x : SturmH lam)) m -
          sturmEigenvalue lam m * (b.repr (x : SturmH lam)) m := by ring
      _ = 0 := sub_eq_zero.mpr hdiag
  exact (mul_eq_zero.mp hmul).resolve_left hdiff

/-- Any eigenvector of the genuine closed operator is orthogonal to
every normalized Gegenbauer mode of a different degree. -/
theorem sturmRealClosed_eigenvector_orthogonal_other_modes
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : (sturmRealPartialOperator lam hlam).closure x =
      sturmEigenvalue lam n • (x : SturmH lam))
    (m : ℕ) (hm : m ≠ n) :
    inner ℝ (sturmMonicEigenCandidate_realL2_normalized lam hlam m)
      (x : SturmH lam) = 0 := by
  have hcoord :=
    sturmRealClosed_eigenvector_single_degree_support
      lam hlam n x hx m hm
  have hb :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam) m =
        sturmMonicEigenCandidate_realL2_normalized lam hlam m := by
    simp only [sturmMonicEigenCandidate_realL2_hilbertBasis,
      HilbertBasis.coe_mkOfOrthogonalEqBot]
  rw [← hb]
  simpa only [HilbertBasis.repr_apply_apply] using hcoord

/-- Arbitrary closed-domain eigenvectors at distinct Gegenbauer degrees
are orthogonal, not merely the constructed polynomial eigenmodes. -/
theorem sturmRealClosed_distinct_degree_eigenvectors_orthogonal
    (lam : ℝ) (hlam : 0 < lam) (n m : ℕ) (hnm : n ≠ m)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : (sturmRealPartialOperator lam hlam).closure x =
      sturmEigenvalue lam n • (x : SturmH lam))
    (hy : (sturmRealPartialOperator lam hlam).closure y =
      sturmEigenvalue lam m • (y : SturmH lam)) :
    inner ℝ (x : SturmH lam) (y : SturmH lam) = 0 := by
  have hs :=
    sturmRealPartialOperator_closure_symmetric lam hlam x y
  rw [hx, hy, real_inner_smul_left, real_inner_smul_right] at hs
  have hne : sturmEigenvalue lam n ≠ sturmEigenvalue lam m := by
    intro heq
    exact hnm (sturmEigenvalue_injective lam hlam heq)
  have hmul :
      (sturmEigenvalue lam n - sturmEigenvalue lam m) *
        inner ℝ (x : SturmH lam) (y : SturmH lam) = 0 := by
    calc
      _ = sturmEigenvalue lam n *
            inner ℝ (x : SturmH lam) (y : SturmH lam) -
          sturmEigenvalue lam m *
            inner ℝ (x : SturmH lam) (y : SturmH lam) := by ring
      _ = 0 := sub_eq_zero.mpr hs
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_eigenvector_single_degree_support
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_eigenvector_orthogonal_other_modes
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_distinct_degree_eigenvectors_orthogonal

end GegenbauerFock.Ultraspherical
