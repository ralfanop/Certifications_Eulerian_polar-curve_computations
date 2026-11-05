import GegenbauerFock.PhyslibTraceClassFiniteNormBound

/-!
# V007 — quantitative stability of finite trace-class combinations

The certified complex normed Schatten-S₁ carrier admits exact
Lipschitz estimates with respect to perturbations of either scalar
coefficients or trace-class summands. These are valid for arbitrary
nonpositive, nonnormal, noncommuting CFC trace-class operators on
any complete complex Hilbert space.

This module uses only finite sums and the already verified genuine
S₁ normed-space structure, NOT the still-pending Banach completeness
instance. Every estimate is measured in actual CFC trace norm.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Perturbing the complex coefficients of a finite linear combination
changes its genuine S₁ norm by at most the weighted coefficient variation. -/
theorem traceNorm_finset_coefficients_perturbation_le
    {ι : Type*} (s : Finset ι) (c d : ι → ℂ)
    (T : ι → TraceClass H) :
    traceNorm H ((∑ i ∈ s, c i • T i) - (∑ i ∈ s, d i • T i)) ≤
      ∑ i ∈ s, ‖c i - d i‖ * traceNorm H (T i) := by
  have h := traceNorm_finset_smul_sum_le (H := H) s
    (fun i => c i - d i) T
  simpa only [sub_smul, Finset.sum_sub_distrib] using h

/-- Perturbing the trace-class summands of a finite combination
is controlled by the weighted sum of the individual S₁ errors. -/
theorem traceNorm_finset_operators_perturbation_le
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (T V : ι → TraceClass H) :
    traceNorm H ((∑ i ∈ s, c i • T i) - (∑ i ∈ s, c i • V i)) ≤
      ∑ i ∈ s, ‖c i‖ * traceNorm H (T i - V i) := by
  have h := traceNorm_finset_smul_sum_le (H := H) s
    c (fun i => T i - V i)
  simpa only [smul_sub, Finset.sum_sub_distrib] using h

#print axioms ProbabilisticTheory.TraceClass.traceNorm_finset_coefficients_perturbation_le
#print axioms ProbabilisticTheory.TraceClass.traceNorm_finset_operators_perturbation_le

end ProbabilisticTheory.TraceClass
