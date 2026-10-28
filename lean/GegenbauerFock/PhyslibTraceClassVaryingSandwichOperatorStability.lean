import GegenbauerFock.PhyslibTraceClassVaryingSandwichSeries

/-!
# V007 — infinite S₁ series under varying operator and scalar perturbations

The bounded left/right multipliers Aᵢ, Bᵢ may vary with the index.
Both changing the trace-class input Tᵢ to Vᵢ and changing scalar
coefficients cᵢ to dᵢ admit exact coefficient-one trace-norm
Lipschitz bounds for the infinite series.

No selfadjointness, positivity, finite rank or common eigenbasis
is required; all sums are formed in the genuine CFC S₁ Banach space.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The fixed-index trace-class input perturbation passes through
the bounded two-sided S₁ action with the ideal norm estimate. -/
theorem norm_weighted_sandwich_input_sub_le_v007
    (c : ℂ) (T V : TraceClass H) (A B : H →L[ℂ] H) :
    ‖c • sandwich T A B - c • sandwich V A B‖ ≤
      ‖c‖ * (‖A‖ * ‖B‖ * traceNorm H (T - V)) := by
  have hs :
      sandwich T A B - sandwich V A B =
        sandwich (T - V) A B := by
    calc
      sandwich T A B - sandwich V A B =
          sandwichContinuous A B T - sandwichContinuous A B V := rfl
      _ = sandwichContinuous A B (T - V) := by rw [map_sub]
      _ = sandwich (T - V) A B := rfl
  calc
    ‖c • sandwich T A B - c • sandwich V A B‖ =
        ‖c • (sandwich T A B - sandwich V A B)‖ := by rw [smul_sub]
    _ = ‖c • sandwich (T - V) A B‖ := by rw [hs]
    _ ≤ ‖c‖ * (‖A‖ * ‖B‖ * traceNorm H (T - V)) :=
      norm_weighted_sandwich_le_v007 c (T - V) A B

/-- True Schatten S₁ stability under indexwise perturbations of
the operator inputs of infinite variable-multiplier series. -/
theorem traceNorm_varying_sandwich_input_tsum_sub_le_v007
    {ι : Type*} (c : ι → ℂ)
    (A B : ι → H →L[ℂ] H) (T V : ι → TraceClass H)
    (hT : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i))))
    (hV : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (V i))))
    (hdelta : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i - V i)))) :
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, c i • sandwich (V i) (A i) (B i))) ≤
      ∑' i : ι, ‖c i‖ *
        (‖A i‖ * ‖B i‖ * traceNorm H (T i - V i)) := by
  have hsT := summable_varying_sandwich_series_v007 c A B T hT
  have hsV := summable_varying_sandwich_series_v007 c A B V hV
  have hsub :
      (∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
        (∑' i : ι, c i • sandwich (V i) (A i) (B i)) =
      ∑' i : ι,
        (c i • sandwich (T i) (A i) (B i) -
         c i • sandwich (V i) (A i) (B i)) :=
    (hsT.tsum_sub hsV).symm
  calc
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, c i • sandwich (V i) (A i) (B i))) =
        ‖(∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
          (∑' i : ι, c i • sandwich (V i) (A i) (B i))‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖∑' i : ι,
        (c i • sandwich (T i) (A i) (B i) -
         c i • sandwich (V i) (A i) (B i))‖ := by rw [hsub]
    _ ≤ ∑' i : ι, ‖c i‖ *
          (‖A i‖ * ‖B i‖ * traceNorm H (T i - V i)) :=
      tsum_of_norm_bounded hdelta.hasSum (fun i =>
        norm_weighted_sandwich_input_sub_le_v007
          (c i) (T i) (V i) (A i) (B i))

/-- True S₁ stability of a variable-multiplier infinite series
under perturbations of its complex scalar coefficients. -/
theorem traceNorm_varying_sandwich_coeff_tsum_sub_le_v007
    {ι : Type*} (c d : ι → ℂ)
    (A B : ι → H →L[ℂ] H) (T : ι → TraceClass H)
    (hc : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i))))
    (hd : Summable (fun i : ι =>
      ‖d i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i))))
    (hdelta : Summable (fun i : ι =>
      ‖c i - d i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i)))) :
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, d i • sandwich (T i) (A i) (B i))) ≤
      ∑' i : ι, ‖c i - d i‖ *
        (‖A i‖ * ‖B i‖ * traceNorm H (T i)) := by
  have hsc := summable_varying_sandwich_series_v007 c A B T hc
  have hsd := summable_varying_sandwich_series_v007 d A B T hd
  have hsub :
      (∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
        (∑' i : ι, d i • sandwich (T i) (A i) (B i)) =
      ∑' i : ι, (c i - d i) • sandwich (T i) (A i) (B i) := by
    calc
      (∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
          (∑' i : ι, d i • sandwich (T i) (A i) (B i)) =
          ∑' i : ι, (c i • sandwich (T i) (A i) (B i) -
            d i • sandwich (T i) (A i) (B i)) :=
        (hsc.tsum_sub hsd).symm
      _ = ∑' i : ι, (c i - d i) • sandwich (T i) (A i) (B i) := by
        apply tsum_congr
        intro i
        exact (sub_smul (c i) (d i) (sandwich (T i) (A i) (B i))).symm
  calc
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, d i • sandwich (T i) (A i) (B i))) =
        ‖(∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
          (∑' i : ι, d i • sandwich (T i) (A i) (B i))‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖∑' i : ι, (c i - d i) • sandwich (T i) (A i) (B i)‖ := by
      rw [hsub]
    _ ≤ ∑' i : ι, ‖c i - d i‖ *
          (‖A i‖ * ‖B i‖ * traceNorm H (T i)) :=
      tsum_of_norm_bounded hdelta.hasSum (fun i =>
        norm_weighted_sandwich_le_v007 (c i - d i)
          (T i) (A i) (B i))

#print axioms ProbabilisticTheory.TraceClass.norm_weighted_sandwich_input_sub_le_v007
#print axioms ProbabilisticTheory.TraceClass.traceNorm_varying_sandwich_input_tsum_sub_le_v007
#print axioms ProbabilisticTheory.TraceClass.traceNorm_varying_sandwich_coeff_tsum_sub_le_v007

end ProbabilisticTheory.TraceClass
