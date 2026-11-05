import GegenbauerFock.UltrasphericalSturmLiouvilleMonicDegree
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialExpansion

/-!
# V007 — algebraic completeness of all-degree monic Gegenbauer polynomials

An arbitrary family of real polynomials of exact degree n with
coefficient one at X^n is triangular with respect to the monomial
basis. Here this is established constructively for the explicit
Gegenbauer eigenpolynomials: every X^n belongs to their real linear
span, hence every real polynomial is in that span.

This is ALGEBRAIC spanning in ℝ[X]. Its transport to genuine weighted
real L² and then Hilbert completeness are separate consequences.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open Polynomial

/-- Every monomial lies in the real-linear span of the explicitly
constructed Gegenbauer eigenpolynomials, with no hypothetical
orthogonal basis or spectral assumptions. -/
theorem sturmMonicEigenCandidate_X_pow_mem_span
    (lam : ℝ) (n : ℕ) :
    (X : ℝ[X]) ^ n ∈
      Submodule.span ℝ (Set.range (sturmMonicEigenCandidate lam)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let S : Submodule ℝ ℝ[X] :=
      Submodule.span ℝ (Set.range (sturmMonicEigenCandidate lam))
    let q : ℝ[X] := sturmMonicEigenCandidate lam n - X ^ n
    have hG : sturmMonicEigenCandidate lam n ∈ S := by
      exact Submodule.subset_span ⟨n, rfl⟩
    have hsmall (k : ℕ) (hk : k ∈ q.support) : k < n := by
      by_contra hnot
      have hle : n ≤ k := Nat.le_of_not_gt hnot
      have hzero : q.coeff k = 0 := by
        rcases eq_or_lt_of_le hle with h_eq | h_gt
        · subst k
          simp [q, sturmMonicEigenCandidate_coeff_top]
        · simp [q, sturmMonicEigenCandidate_coeff_above lam n k h_gt,
            coeff_X_pow, (ne_of_gt h_gt)]
      exact (mem_support_iff.mp hk) hzero
    have hq : q ∈ S := by
      rw [← sturmPolynomial_true_monomial_expansion q]
      exact Submodule.sum_mem S (fun k hk =>
        Submodule.smul_mem S _ (ih k (hsmall k hk)))
    have hx : (X : ℝ[X]) ^ n =
        sturmMonicEigenCandidate lam n - q := by
      dsimp [q]
      abel
    rw [hx]
    exact S.sub_mem hG hq

/-- The explicit all-degree monic Gegenbauer sequence generates
the ENTIRE polynomial algebra as a real vector space. -/
theorem sturmMonicEigenCandidate_span_eq_top (lam : ℝ) :
    Submodule.span ℝ (Set.range (sturmMonicEigenCandidate lam)) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro p
  rw [← sturmPolynomial_true_monomial_expansion p]
  exact Submodule.sum_mem _ (fun k hk =>
    Submodule.smul_mem _ _ (sturmMonicEigenCandidate_X_pow_mem_span lam k))

#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_X_pow_mem_span
#print axioms GegenbauerFock.Ultraspherical.sturmMonicEigenCandidate_span_eq_top

end GegenbauerFock.Ultraspherical
