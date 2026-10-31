import GegenbauerFock.UltrasphericalSturmLiouvilleExactGegenbauerSpectralClosure
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealSpectralModes
import GegenbauerFock.UltrasphericalSturmLiouvilleMonicRealL2Nonzero
import GegenbauerFock.UltrasphericalSturmLiouvilleEigenvalueOrder

/-!
# The first nonconstant Gegenbauer eigenvalue and the closed Sturm spectral gap

For every λ > 0 the concrete degree-one monic Gegenbauer polynomial
is a genuinely nonzero eigenvector in the domain of the canonical
closed real Sturm operator. Its eigenvalue is -(1 + 2λ).

Every positive degree n has eigenvalue <= -(1 + 2λ), and equality
occurs exactly at n = 1; every n >= 2 has strictly smaller eigenvalue.
These facts give the sharp algebraic spectral gap between degree zero
and the remaining *certified actual Hilbert eigenmodes*, without
postulating an eigenbasis or merely considering formal differential
eigenvalues. The exact spectral realization is imported above.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact eigenvalue of the first nonconstant Sturm--Gegenbauer mode. -/
theorem sturmEigenvalue_one_exact (lam : ℝ) :
    sturmEigenvalue lam 1 = -(1 + 2 * lam) := by
  unfold sturmEigenvalue
  ring

/-- The positive-degree eigenvalues are separated from zero by the
sharp constant 1 + 2λ, attained by the degree-one mode. -/
theorem sturmEigenvalue_positive_degree_gap
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : n ≠ 0) :
    sturmEigenvalue lam n ≤ -(1 + 2 * lam) := by
  by_cases h1 : n = 1
  · subst n
    rw [sturmEigenvalue_one_exact]
  · have hlt : 1 < n := by omega
    have hstrict := sturmEigenvalue_strictAnti lam hlam hlt
    rw [sturmEigenvalue_one_exact] at hstrict
    exact le_of_lt hstrict

/-- Every degree at least two lies strictly below the first
nonconstant eigenvalue, so the gap is attained uniquely at n=1. -/
theorem sturmEigenvalue_degree_ge_two_strict
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) (hn : 2 ≤ n) :
    sturmEigenvalue lam n < -(1 + 2 * lam) := by
  have hlt : 1 < n := by omega
  have hstrict := sturmEigenvalue_strictAnti lam hlam hlt
  rw [sturmEigenvalue_one_exact] at hstrict
  exact hstrict

/-- The first nonconstant eigenvalue is realized by a NONZERO
vector in the genuine closed weighted-real-L² Sturm domain. -/
theorem sturmRealClosed_first_nonconstant_eigenmode
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) ≠ 0 ∧
      (sturmRealPartialOperator lam hlam).closure x =
        -(1 + 2 * lam) • (x : SturmH lam) := by
  obtain ⟨x, hx, heig⟩ :=
    sturmMonicEigenCandidate_closed_domain_eigen lam hlam 1
  refine ⟨x, ?_, ?_⟩
  · rw [hx]
    exact sturmMonicEigenCandidate_realL2_ne_zero lam hlam 1
  · rw [sturmEigenvalue_one_exact] at heig
    exact heig

/-- The actual closed differential operator acts on the first
normalized Fourier coordinate with eigenvalue -(1+2λ). -/
theorem sturmRealClosed_first_nonconstant_Fourier_coordinate
    (lam : ℝ) (hlam : 0 < lam)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
      ((sturmRealPartialOperator lam hlam).closure x) 1 =
      -(1 + 2 * lam) *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (x : SturmH lam) 1 := by
  have h := (sturmRealClosed_eq_exact_monicGegenbauer_spectral_realization
    lam hlam).2 x 1
  convert h using 1 <;> ring

#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_one_exact
#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_positive_degree_gap
#print axioms GegenbauerFock.Ultraspherical.sturmEigenvalue_degree_ge_two_strict
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_first_nonconstant_eigenmode
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_first_nonconstant_Fourier_coordinate

end GegenbauerFock.Ultraspherical
