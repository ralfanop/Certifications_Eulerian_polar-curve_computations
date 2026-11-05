import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicFullL2Eigenmodes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Nonzero

/-!
# Exact point eigenvalues of the closed real Gegenbauer Sturm operator

The genuine closure of the real polynomial Sturm differential operator
has precisely the expected point eigenvalues -n(n+2lambda), lambda > 0.
The proof uses the certified complete normalized Gegenbauer Hilbert basis
and the exact coefficient action on the actual closed operator domain.
No hypothetical diagonal extension or spectral-completeness premise occurs.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- A scalar outside the Gegenbauer diagonal cannot have a nonzero
eigenvector for the actual closed differential operator. -/
theorem sturmRealClosed_no_point_eigenvalue_off_Gegenbauer
    (lam : ℝ) (hlam : 0 < lam) (r : ℝ)
    (hr : ∀ n : ℕ, r ≠ sturmEigenvalue lam n)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : (sturmRealPartialOperator lam hlam).closure x =
      r • (x : SturmH lam)) :
    (x : SturmH lam) = 0 := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hrepr : b.repr (x : SturmH lam) = 0 := by
    ext n
    have hdiag :=
      (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
        lam hlam).2 x n
    change (b.repr ((sturmRealPartialOperator lam hlam).closure x)) n =
      sturmEigenvalue lam n * (b.repr (x : SturmH lam)) n at hdiag
    rw [hx, map_smul] at hdiag
    change r * (b.repr (x : SturmH lam)) n =
      sturmEigenvalue lam n * (b.repr (x : SturmH lam)) n at hdiag
    have hnonzero : r - sturmEigenvalue lam n ≠ 0 :=
      sub_ne_zero.mpr (hr n)
    have hfact :
        (r - sturmEigenvalue lam n) *
          (b.repr (x : SturmH lam)) n = 0 := by
      calc
        _ = r * (b.repr (x : SturmH lam)) n -
          sturmEigenvalue lam n * (b.repr (x : SturmH lam)) n := by ring
        _ = 0 := sub_eq_zero.mpr hdiag
    have hc : (b.repr (x : SturmH lam)) n = 0 :=
      (mul_eq_zero.mp hfact).resolve_left hnonzero
    simpa using hc
  apply b.repr.injective
  simpa only [map_zero] using hrepr

/-- Every concrete Gegenbauer diagonal value has a nonzero
eigenvector in the canonical closed Sturm graph. -/
theorem sturmRealClosed_has_Gegenbauer_eigenvector
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmRealPartialOperator lam hlam).closure x =
        sturmEigenvalue lam n • (x : SturmH lam) := by
  obtain ⟨x, hx, hAx⟩ :=
    sturmRealClosed_monic_all_degree_eigenmode lam hlam n
  refine ⟨x, ?_, hAx⟩
  rw [hx]
  exact sturmMonicEigenCandidate_realL2_ne_zero lam hlam n

/-- Exact classification of real point eigenvalues for the
canonical closed Gegenbauer Sturm differential operator. -/
theorem sturmRealClosed_point_eigenvalue_iff_Gegenbauer
    (lam : ℝ) (hlam : 0 < lam) (r : ℝ) :
    (∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmRealPartialOperator lam hlam).closure x =
        r • (x : SturmH lam)) ↔
    ∃ n : ℕ, r = sturmEigenvalue lam n := by
  constructor
  · rintro ⟨x, hnonzero, heig⟩
    by_contra hnone
    push_neg at hnone
    exact hnonzero
      (sturmRealClosed_no_point_eigenvalue_off_Gegenbauer
        lam hlam r hnone x heig)
  · rintro ⟨n, rfl⟩
    exact sturmRealClosed_has_Gegenbauer_eigenvector lam hlam n

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_no_point_eigenvalue_off_Gegenbauer
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_has_Gegenbauer_eigenvector
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_point_eigenvalue_iff_Gegenbauer

end GegenbauerFock.Ultraspherical
