import GegenbauerFock.PhyslibTraceClassWeightedInfiniteSeries

/-!
# V007 — infinite weighted Schatten-S₁ coefficient and operator stability

Infinite complex-weighted trace-class series satisfy exact Lipschitz
bounds for perturbing the coefficients or the operator summands.
No positivity, finite rank, commutativity or preferred basis is assumed.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Variation of scalar coefficients in arbitrary infinite S₁ series. -/
theorem traceNorm_weighted_tsum_coefficients_perturbation_le
    {ι : Type*} (c d : ι → ℂ) (T : ι → TraceClass H)
    (hc : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i)))
    (hd : Summable (fun i : ι => ‖d i‖ * traceNorm H (T i)))
    (hdelta : Summable (fun i : ι => ‖c i - d i‖ * traceNorm H (T i))) :
    traceNorm H ((∑' i : ι, c i • T i) - (∑' i : ι, d i • T i)) ≤
      ∑' i : ι, ‖c i - d i‖ * traceNorm H (T i) := by
  have hc' := summable_weighted_traceClass_series (H := H) c T hc
  have hd' := summable_weighted_traceClass_series (H := H) d T hd
  have hsum :
      (∑' i : ι, c i • T i) - (∑' i : ι, d i • T i) =
        ∑' i : ι, (c i - d i) • T i := by
    calc
      (∑' i : ι, c i • T i) - (∑' i : ι, d i • T i) =
          ∑' i : ι, (c i • T i - d i • T i) :=
        (hc'.tsum_sub hd').symm
      _ = ∑' i : ι, (c i - d i) • T i := by
        apply tsum_congr
        intro i
        exact (sub_smul (c i) (d i) (T i)).symm
  rw [hsum]
  exact traceNorm_weighted_tsum_le (H := H)
    (fun i => c i - d i) T hdelta

/-- Variation of S₁ summands in arbitrary infinite weighted series. -/
theorem traceNorm_weighted_tsum_operators_perturbation_le
    {ι : Type*} (c : ι → ℂ) (T V : ι → TraceClass H)
    (hT : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i)))
    (hV : Summable (fun i : ι => ‖c i‖ * traceNorm H (V i)))
    (hdelta : Summable (fun i : ι => ‖c i‖ * traceNorm H (T i - V i))) :
    traceNorm H ((∑' i : ι, c i • T i) - (∑' i : ι, c i • V i)) ≤
      ∑' i : ι, ‖c i‖ * traceNorm H (T i - V i) := by
  have hT' := summable_weighted_traceClass_series (H := H) c T hT
  have hV' := summable_weighted_traceClass_series (H := H) c V hV
  have hsum :
      (∑' i : ι, c i • T i) - (∑' i : ι, c i • V i) =
        ∑' i : ι, c i • (T i - V i) := by
    calc
      (∑' i : ι, c i • T i) - (∑' i : ι, c i • V i) =
          ∑' i : ι, (c i • T i - c i • V i) :=
        (hT'.tsum_sub hV').symm
      _ = ∑' i : ι, c i • (T i - V i) := by
        apply tsum_congr
        intro i
        exact (smul_sub (c i) (T i) (V i)).symm
  rw [hsum]
  exact traceNorm_weighted_tsum_le (H := H) c
    (fun i => T i - V i) hdelta

#print axioms ProbabilisticTheory.TraceClass.traceNorm_weighted_tsum_coefficients_perturbation_le
#print axioms ProbabilisticTheory.TraceClass.traceNorm_weighted_tsum_operators_perturbation_le

end ProbabilisticTheory.TraceClass
