import GegenbauerFock.PhyslibTraceClassWeightedInfiniteSeries
import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# V007 — bounded bilateral maps commute with weighted infinite S₁ sums

In the certified complex Schatten-S₁ Banach space, absolutely
trace-norm convergent weighted families remain convergent after
multiplication on both sides by fixed bounded Hilbert endomorphisms.

The continuous bilateral CFC S₁ map commutes with the actual infinite
trace-norm sum. An exact constant-one norm inequality controls the
resulting sum by the product of the two multiplier norms.

This holds for arbitrary nonpositive, nonnormal and noncommuting
trace-class summands, without a preferred Hilbert basis.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Trace-norm summability of the weighted S₁ series is preserved
by each fixed pair of bounded left and right multipliers. -/
theorem summable_weighted_sandwich_series
    {ι : Type*} (A B : H →L[ℂ] H)
    (c : ι → ℂ) (T : ι → TraceClass H)
    (h : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i))) :
    Summable (fun i : ι => c i • sandwich (T i) A B) := by
  have hs := summable_weighted_traceClass_series (H := H) c T h
  have hs' := hs.mapL (sandwichContinuous A B)
  simpa only [map_smul, sandwichContinuous_apply] using hs'

/-- The bounded bilateral CFC action commutes with an infinite
complex-weighted sum in the genuine Schatten S₁ topology. -/
theorem sandwich_weighted_tsum
    {ι : Type*} (A B : H →L[ℂ] H)
    (c : ι → ℂ) (T : ι → TraceClass H)
    (h : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i))) :
    sandwich (∑' i : ι, c i • T i) A B =
      ∑' i : ι, c i • sandwich (T i) A B := by
  have hs := summable_weighted_traceClass_series (H := H) c T h
  have hm := (sandwichContinuous A B).map_tsum hs
  simpa only [sandwichContinuous_apply, map_smul] using hm

/-- An infinite bilateral S₁ operator series satisfies the sharp
trace-norm ideal bound with the same constant one as finite sums. -/
theorem traceNorm_weighted_sandwich_tsum_le
    {ι : Type*} (A B : H →L[ℂ] H)
    (c : ι → ℂ) (T : ι → TraceClass H)
    (h : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i))) :
    traceNorm H (∑' i : ι, c i • sandwich (T i) A B) ≤
      (‖A‖ * ‖B‖) * (∑' i : ι, ‖c i‖ * traceNorm H (T i)) := by
  have ht :
      ‖∑' i : ι, c i • T i‖ ≤
        ∑' i : ι, ‖c i‖ * traceNorm H (T i) := by
    simpa only [norm_eq_genuineTraceNorm] using
      (traceNorm_weighted_tsum_le (H := H) c T h)
  calc
    traceNorm H (∑' i : ι, c i • sandwich (T i) A B) =
        ‖sandwichContinuous A B (∑' i : ι, c i • T i)‖ := by
      rw [sandwichContinuous_apply, sandwich_weighted_tsum A B c T h]
      exact (norm_eq_genuineTraceNorm _).symm
    _ ≤ ‖sandwichContinuous A B‖ *
          ‖∑' i : ι, c i • T i‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖A‖ * ‖B‖) * ‖∑' i : ι, c i • T i‖ :=
      mul_le_mul_of_nonneg_right
        (sandwichContinuous_norm_le A B) (norm_nonneg _)
    _ ≤ (‖A‖ * ‖B‖) *
          (∑' i : ι, ‖c i‖ * traceNorm H (T i)) :=
      mul_le_mul_of_nonneg_left ht
        (mul_nonneg (norm_nonneg A) (norm_nonneg B))

#print axioms ProbabilisticTheory.TraceClass.summable_weighted_sandwich_series
#print axioms ProbabilisticTheory.TraceClass.sandwich_weighted_tsum
#print axioms ProbabilisticTheory.TraceClass.traceNorm_weighted_sandwich_tsum_le

end ProbabilisticTheory.TraceClass
