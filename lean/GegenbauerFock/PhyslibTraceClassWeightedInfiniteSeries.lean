import GegenbauerFock.PhyslibTraceClassInfiniteSeries

/-!
# V007 — absolutely summable complex-weighted CFC Schatten-S₁ series

The genuine trace-normed space of arbitrary (possibly nonnormal and
noncommuting) CFC trace-class operators is a certified complex Banach
space. Complex coefficients may therefore be used to form infinite
trace-class linear combinations whenever the weighted sum of true
trace norms is finite.

Neither finite-dimensionality, positivity, nor a common eigenbasis
is required. No new axiom or assumption of summability in the weaker
operator norm is introduced.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem traceNorm_smul_weighted_v007
    (c : ℂ) (T : TraceClass H) :
    traceNorm H (c • T) = ‖c‖ * traceNorm H T := by
  calc
    traceNorm H (c • T) = ‖c • T‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖c‖ * ‖T‖ := norm_smul c T
    _ = ‖c‖ * traceNorm H T := by
      rw [norm_eq_genuineTraceNorm]

/-- Weighted absolute CFC trace-norm summability implies convergence
of the operator series in the genuine S₁ Banach topology. -/
theorem summable_weighted_traceClass_series
    {ι : Type*} (c : ι → ℂ) (T : ι → TraceClass H)
    (h : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i))) :
    Summable (fun i : ι => c i • T i) := by
  apply summable_of_summable_traceNorm (H := H)
  simpa only [traceNorm_smul_weighted_v007] using h

/-- The quantitative infinite weighted Schatten-S₁ triangle
inequality, with exact CFC trace norms on both sides. -/
theorem traceNorm_weighted_tsum_le
    {ι : Type*} (c : ι → ℂ) (T : ι → TraceClass H)
    (h : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i))) :
    traceNorm H (∑' i : ι, c i • T i) ≤
      ∑' i : ι, ‖c i‖ * traceNorm H (T i) := by
  have hs : Summable (fun i : ι => traceNorm H (c i • T i)) := by
    simpa only [traceNorm_smul_weighted_v007] using h
  simpa only [traceNorm_smul_weighted_v007] using
    (traceNorm_tsum_le_tsum_traceNorm (H := H)
      (fun i : ι => c i • T i) hs)

#print axioms ProbabilisticTheory.TraceClass.summable_weighted_traceClass_series
#print axioms ProbabilisticTheory.TraceClass.traceNorm_weighted_tsum_le

end ProbabilisticTheory.TraceClass
