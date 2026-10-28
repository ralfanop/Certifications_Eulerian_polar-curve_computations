import GegenbauerFock.PhyslibTraceClassSandwichWeightedTsum

/-!
# V007 — varying bilateral multiplier families in infinite CFC S₁ sums

Unlike the fixed A, B continuous-linear-map interchange theorem,
the bounded multipliers in this result vary with the index.

The summability condition is the exact weighted three-factor
Schatten-ideal majorant. Its finiteness ensures convergence in the
genuine, now-certified Schatten S₁ complex Banach topology,
without positivity, commutativity, finite rank, or a shared basis.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Each index-dependent two-sided ideal term is controlled by its
own two multiplier norms, in the actual functional-calculus S₁ norm. -/
theorem norm_weighted_sandwich_le_v007
    (c : ℂ) (T : TraceClass H) (A B : H →L[ℂ] H) :
    ‖c • sandwich T A B‖ ≤
      ‖c‖ * (‖A‖ * ‖B‖ * traceNorm H T) := by
  have hs : ‖sandwich T A B‖ ≤ (‖A‖ * ‖B‖) * ‖T‖ := by
    calc
      ‖sandwich T A B‖ = ‖sandwichContinuous A B T‖ := rfl
      _ ≤ ‖sandwichContinuous A B‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖A‖ * ‖B‖) * ‖T‖ :=
        mul_le_mul_of_nonneg_right
          (sandwichContinuous_norm_le A B) (norm_nonneg _)
  calc
    ‖c • sandwich T A B‖ = ‖c‖ * ‖sandwich T A B‖ := norm_smul c _
    _ ≤ ‖c‖ * ((‖A‖ * ‖B‖) * ‖T‖) :=
      mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = ‖c‖ * (‖A‖ * ‖B‖ * traceNorm H T) := by
      rw [norm_eq_genuineTraceNorm]

/-- A varying family of bounded left/right multipliers produces a
genuinely trace-norm summable series when its exact majorant is
summable. -/
theorem summable_varying_sandwich_series_v007
    {ι : Type*} (c : ι → ℂ)
    (A B : ι → H →L[ℂ] H) (T : ι → TraceClass H)
    (h : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i)))) :
    Summable (fun i : ι => c i • sandwich (T i) (A i) (B i)) := by
  exact h.of_norm_bounded (fun i =>
    norm_weighted_sandwich_le_v007 (c i) (T i) (A i) (B i))

/-- Trace-norm ideal triangle for index-dependent bilateral
multipliers, with the optimal universal coefficient one. -/
theorem traceNorm_varying_sandwich_tsum_le_v007
    {ι : Type*} (c : ι → ℂ)
    (A B : ι → H →L[ℂ] H) (T : ι → TraceClass H)
    (h : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i)))) :
    traceNorm H (∑' i : ι, c i • sandwich (T i) (A i) (B i)) ≤
      ∑' i : ι, ‖c i‖ *
        (‖A i‖ * ‖B i‖ * traceNorm H (T i)) := by
  calc
    traceNorm H (∑' i : ι, c i • sandwich (T i) (A i) (B i)) =
        ‖∑' i : ι, c i • sandwich (T i) (A i) (B i)‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ ≤ ∑' i : ι, ‖c i‖ *
          (‖A i‖ * ‖B i‖ * traceNorm H (T i)) :=
      tsum_of_norm_bounded h
        (fun i => norm_weighted_sandwich_le_v007
          (c i) (T i) (A i) (B i))

#print axioms ProbabilisticTheory.TraceClass.norm_weighted_sandwich_le_v007
#print axioms ProbabilisticTheory.TraceClass.summable_varying_sandwich_series_v007
#print axioms ProbabilisticTheory.TraceClass.traceNorm_varying_sandwich_tsum_le_v007

end ProbabilisticTheory.TraceClass
