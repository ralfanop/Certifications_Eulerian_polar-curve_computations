import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — bounded inclusion of the true trace-normed S1 space

The identity inclusion from a trace-class operator with its genuine
Physlib-compatible CFC trace norm to the ambient bounded Hilbert
endomorphisms is a continuous complex-linear map of norm at most 1.
This is the essential analytic first step in proving S1 completeness:
an S1-Cauchy sequence is Cauchy in ambient operator norm.

The construction assumes only the separately formalized S1 normed-space
structure and the kernel-checked inequality `‖T‖op ≤ ‖T‖₁`.
It makes no unsupported claim that S1 is already complete.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable (H : Type*)
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact underlying bounded operator of a source-compatible
trace-class element, as a continuous complex-linear map. -/
noncomputable def inclusion :
    TraceClass H →L[ℂ] (H →L[ℂ] H) :=
  ({ toFun := fun T => T.1
     map_add' := by
       intro T S
       rfl
     map_smul' := by
       intro c T
       rfl
    } : TraceClass H →ₗ[ℂ] (H →L[ℂ] H)).mkContinuous 1 (by
      intro T
      change ‖T.1‖ ≤ 1 * ‖T‖
      simpa only [one_mul, norm_eq_genuineTraceNorm] using
        (ProbabilisticTheory.operatorNorm_le_traceNorm_via_sqrt_abs T.1 T.2))

@[simp] theorem inclusion_apply (T : TraceClass H) :
    inclusion H T = T.1 := rfl

/-- The sharp upper bound for the inclusion operator norm. -/
theorem inclusion_norm_le_one : ‖inclusion H‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro T
  change ‖T.1‖ ≤ 1 * ‖T‖
  simpa only [one_mul, norm_eq_genuineTraceNorm] using
    (ProbabilisticTheory.operatorNorm_le_traceNorm_via_sqrt_abs T.1 T.2)

/-- Quantitative ambient-operator convergence control: an S₁
difference has no larger bounded-operator norm than its genuine
CFC trace norm. This estimate is the Cauchy-sequence prerequisite
for eventual Schatten S₁ Banach completeness. -/
theorem opNorm_sub_le_traceNorm_sub (T V : TraceClass H) :
    ‖T.1 - V.1‖ ≤ ‖T - V‖ := by
  have h := ProbabilisticTheory.operatorNorm_le_traceNorm_via_sqrt_abs
    (T - V).1 (T - V).2
  simpa only [sub_operator, norm_eq_genuineTraceNorm] using h

/-- The underlying-operator inclusion contracts the actual metric
distance induced by the CFC trace norm. -/
theorem dist_operator_le_dist (T V : TraceClass H) :
    dist T.1 V.1 ≤ dist T V := by
  simpa only [dist_eq_norm] using opNorm_sub_le_traceNorm_sub H T V

#print axioms ProbabilisticTheory.TraceClass.opNorm_sub_le_traceNorm_sub
#print axioms ProbabilisticTheory.TraceClass.dist_operator_le_dist

#print axioms ProbabilisticTheory.TraceClass.inclusion_apply
#print axioms ProbabilisticTheory.TraceClass.inclusion_norm_le_one

end ProbabilisticTheory.TraceClass
