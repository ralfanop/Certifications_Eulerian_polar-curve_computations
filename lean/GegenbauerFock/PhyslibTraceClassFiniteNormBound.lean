import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — quantitative CFC trace-norm bounds for finite S₁ combinations

The independently certified general CFC Schatten-S₁ triangle inequality
and complex scalar homogeneity imply sharp finite-sum estimates.

These results operate on the *actual* proof-carrying infinite-dimensional
Physlib-compatible trace-class subtype, whose norm is the true
functional-calculus trace norm, not the bounded operator norm.
They are valid for arbitrary non-selfadjoint terms, without a shared
basis, positivity or commutativity.

The finite bounds help control trace-norm Cauchy tails in the separate
Banach completeness certification; they DO NOT assume or assert
Banach completeness.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The genuine CFC trace norm of an arbitrary finite sum is
bounded by the sum of the genuine trace norms of its summands. -/
theorem traceNorm_finset_sum_le
    {ι : Type*} (s : Finset ι) (T : ι → TraceClass H) :
    traceNorm H (∑ i ∈ s, T i) ≤
      ∑ i ∈ s, traceNorm H (T i) := by
  calc
    traceNorm H (∑ i ∈ s, T i) =
        ‖∑ i ∈ s, T i‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ ≤ ∑ i ∈ s, ‖T i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, traceNorm H (T i) := by
      simp only [norm_eq_genuineTraceNorm]

/-- Weighted finite Young/triangle bound for arbitrary complex
linear combinations of nonpositive trace-class operators. -/
theorem traceNorm_finset_smul_sum_le
    {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (T : ι → TraceClass H) :
    traceNorm H (∑ i ∈ s, c i • T i) ≤
      ∑ i ∈ s, ‖c i‖ * traceNorm H (T i) := by
  calc
    traceNorm H (∑ i ∈ s, c i • T i) =
        ‖∑ i ∈ s, c i • T i‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ ≤ ∑ i ∈ s, ‖c i • T i‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, ‖c i‖ * traceNorm H (T i) := by
      simp only [norm_smul, norm_eq_genuineTraceNorm]

#print axioms ProbabilisticTheory.TraceClass.traceNorm_finset_sum_le
#print axioms ProbabilisticTheory.TraceClass.traceNorm_finset_smul_sum_le

end ProbabilisticTheory.TraceClass
