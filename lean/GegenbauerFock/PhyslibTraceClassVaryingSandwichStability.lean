import GegenbauerFock.PhyslibTraceClassVaryingSandwichSeries
import GegenbauerFock.PhyslibTraceClassSandwichMultiplierStability

/-!
# V007 — stability of infinite CFC S₁ sandwiches under varying multipliers

For arbitrary complex coefficients and index-dependent bounded Aᵢ,Bᵢ,Cᵢ,Dᵢ,
the exact genuine trace-norm difference of infinite sums is controlled by
the absolutely summable indexwise bilateral perturbation majorant:

  Σᵢ ‖cᵢ‖ (‖Aᵢ-Cᵢ‖‖Bᵢ‖ + ‖Cᵢ‖‖Bᵢ-Dᵢ‖) ‖Tᵢ‖₁.

There are no positivity, finite-rank, commutativity, or common-basis
assumptions. Importantly, the sums converge in S₁ Banach trace norm.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pointwise joint multiplier perturbation inequality, with the
universal coefficient one, for an arbitrary complex-weighted S₁ term. -/
theorem norm_weighted_sandwich_multiplier_sub_le_v007
    (c : ℂ) (T : TraceClass H)
    (A B C D : H →L[ℂ] H) :
    ‖c • sandwich T A B - c • sandwich T C D‖ ≤
      ‖c‖ * ((‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖) * traceNorm H T) := by
  calc
    ‖c • sandwich T A B - c • sandwich T C D‖ =
        ‖c • (sandwich T A B - sandwich T C D)‖ := by
      rw [smul_sub]
    _ = ‖c‖ * ‖sandwich T A B - sandwich T C D‖ := norm_smul c _
    _ ≤ ‖c‖ * ((‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖) * ‖T‖) :=
      mul_le_mul_of_nonneg_left
        (sandwich_multiplier_sub_norm_le T A B C D) (norm_nonneg _)
    _ = ‖c‖ * ((‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖) * traceNorm H T) := by
      rw [norm_eq_genuineTraceNorm]

/-- The difference family is S₁-summable whenever the separate
bilateral families and the true S₁ variation majorant are summable. -/
theorem summable_varying_sandwich_multiplier_difference_v007
    {ι : Type*} (c : ι → ℂ)
    (A B C D : ι → H →L[ℂ] H) (T : ι → TraceClass H)
    (hdelta : Summable (fun i : ι =>
      ‖c i‖ * ((‖A i - C i‖ * ‖B i‖ +
        ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i)))) :
    Summable (fun i : ι =>
      c i • sandwich (T i) (A i) (B i) -
      c i • sandwich (T i) (C i) (D i)) := by
  exact hdelta.of_norm_bounded (fun i =>
    norm_weighted_sandwich_multiplier_sub_le_v007
      (c i) (T i) (A i) (B i) (C i) (D i))

/-- Quantitative stability of TWO infinite trace-class sums under
joint index-dependent perturbations of their bounded multipliers. -/
theorem traceNorm_varying_sandwich_multiplier_tsum_sub_le_v007
    {ι : Type*} (c : ι → ℂ)
    (A B C D : ι → H →L[ℂ] H) (T : ι → TraceClass H)
    (hAB : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i))))
    (hCD : Summable (fun i : ι =>
      ‖c i‖ * (‖C i‖ * ‖D i‖ * traceNorm H (T i))))
    (hdelta : Summable (fun i : ι =>
      ‖c i‖ * ((‖A i - C i‖ * ‖B i‖ +
        ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i)))) :
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, c i • sandwich (T i) (C i) (D i))) ≤
    ∑' i : ι, ‖c i‖ *
      ((‖A i - C i‖ * ‖B i‖ +
        ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i)) := by
  have hsAB := summable_varying_sandwich_series_v007 c A B T hAB
  have hsCD := summable_varying_sandwich_series_v007 c C D T hCD
  have hsub :
      (∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
        (∑' i : ι, c i • sandwich (T i) (C i) (D i)) =
      ∑' i : ι, (c i • sandwich (T i) (A i) (B i) -
        c i • sandwich (T i) (C i) (D i)) :=
    (hsAB.tsum_sub hsCD).symm
  calc
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, c i • sandwich (T i) (C i) (D i))) =
        ‖(∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
          (∑' i : ι, c i • sandwich (T i) (C i) (D i))‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖∑' i : ι, (c i • sandwich (T i) (A i) (B i) -
        c i • sandwich (T i) (C i) (D i))‖ := by
      rw [hsub]
    _ ≤ ∑' i : ι, ‖c i‖ *
        ((‖A i - C i‖ * ‖B i‖ +
          ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i)) :=
      tsum_of_norm_bounded hdelta.hasSum (fun i =>
        norm_weighted_sandwich_multiplier_sub_le_v007
          (c i) (T i) (A i) (B i) (C i) (D i))

#print axioms ProbabilisticTheory.TraceClass.norm_weighted_sandwich_multiplier_sub_le_v007
#print axioms ProbabilisticTheory.TraceClass.summable_varying_sandwich_multiplier_difference_v007
#print axioms ProbabilisticTheory.TraceClass.traceNorm_varying_sandwich_multiplier_tsum_sub_le_v007

end ProbabilisticTheory.TraceClass
