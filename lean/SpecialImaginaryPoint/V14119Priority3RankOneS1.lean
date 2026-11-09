import SpecialImaginaryPoint.V14119Priority3TraceClassModel

/-!
# Manuscript 14.119 Priority 3 — trace norm of actual rank-one spectral summands

The genuine positive Dirichlet inverse on complex l² is already
certified as CFC-absolute Schatten S₁. This module strengthens its
spectral expansion by showing that EACH individual actual rank-one
summand is S₁ with exact trace norm σ(n). No diagonal surrogate or
new trace-class predicate is introduced.

The Fredholm determinant of an arbitrary trace-class operator and
the PDE Dirichlet realisation on L²(0,1) remain separate obligations.
-/

noncomputable section

namespace Manuscript14Priority3.TraceClassModel
open Filter Topology InnerProductSpace
open scoped ComplexOrder lp

/-- The true Hilbert basis diagonal of a single rank-one spectral
summand is supported at its own basis index. -/
theorem term_diagonal (n k : ℕ) :
    (inner ℂ (b k) ((term n) (b k))).re =
      if k = n then σ n else 0 := by
  by_cases h : k = n
  · subst k
    change (inner ℂ (b n)
      (((σ n : ℂ) • rankOne ℂ (b n) (b n)) (b n))).re = _
    rw [smul_apply, rankOne_apply]
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one n]
  · have hnk : n ≠ k := Ne.symm h
    change (inner ℂ (b k)
      (((σ n : ℂ) • rankOne ℂ (b n) (b n)) (b k))).re = _
    rw [smul_apply, rankOne_apply, b.orthonormal.inner_eq_zero hnk]
    simp [h]

/-- A single true rank-one Hilbert-space summand is CFC trace class. -/
theorem term_isTraceClass (n : ℕ) :
    ProbabilisticTheory.IsTraceClass (term n) := by
  have hpos : (0 : H →L[ℂ] H) ≤ term n :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2 (term_isPositive n)
  have hdiag :
      Summable (fun k : ℕ => (inner ℂ (b k) ((term n) (b k))).re) := by
    apply summable_of_ne_finset_zero (s := {n})
    intro k hk
    rw [term_diagonal]
    have hne : k ≠ n := by simpa using hk
    simp [hne]
  exact GegenbauerFock.Ultraspherical.complex_nonneg_isTraceClass_of_summable_natBasis_diagonal
      (term n) hpos b hdiag

/-- Exact CFC-absolute genuine Schatten-S₁ norm of each summand,
equal to the positive inverse eigenvalue. -/
theorem term_traceNorm_eq (n : ℕ) :
    ProbabilisticTheory.traceNorm (term n) (term_isTraceClass n) = σ n := by
  have hpos : (0 : H →L[ℂ] H) ≤ term n :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2 (term_isPositive n)
  rw [GegenbauerFock.HilbertSchmidtBasis.positiveTrace_traceNorm_eq_diagonal_tsum
      (term n) (term_isTraceClass n) hpos b]
  rw [tsum_eq_single n]
  · simpa using term_diagonal n n
  · intro k hk
    simpa [hk] using term_diagonal n k

#print axioms Manuscript14Priority3.TraceClassModel.term_diagonal
#print axioms Manuscript14Priority3.TraceClassModel.term_isTraceClass
#print axioms Manuscript14Priority3.TraceClassModel.term_traceNorm_eq

end Manuscript14Priority3.TraceClassModel
