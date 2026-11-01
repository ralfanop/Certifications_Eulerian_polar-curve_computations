import GegenbauerFock.PhyslibTraceClassJointInfiniteStability
import GegenbauerFock.PhyslibTraceClassSeriesOperatorConvergence

/-!
# V007 — ambient operator-norm stability of jointly perturbed S₁ series

The independently formalized three-axis Schatten S₁ Lipschitz
bound dominates the same difference in ambient B(H) operator norm,
with the identical explicit summable coefficient-one majorant.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Simultaneous perturbation of coefficients, both multipliers,
and trace-class inputs, measured in ambient operator norm. -/
theorem operatorNorm_joint_varying_sandwich_tsum_le_v007
    {ι : Type*} (c d : ι → ℂ)
    (A B C D : ι → H →L[ℂ] H)
    (T V : ι → TraceClass H)
    (hAT : Summable (fun i : ι =>
      ‖c i‖ * (‖A i‖ * ‖B i‖ * traceNorm H (T i))))
    (hCT : Summable (fun i : ι =>
      ‖c i‖ * (‖C i‖ * ‖D i‖ * traceNorm H (T i))))
    (hCV : Summable (fun i : ι =>
      ‖c i‖ * (‖C i‖ * ‖D i‖ * traceNorm H (V i))))
    (hDV : Summable (fun i : ι =>
      ‖d i‖ * (‖C i‖ * ‖D i‖ * traceNorm H (V i))))
    (hMult : Summable (fun i : ι =>
      ‖c i‖ * ((‖A i - C i‖ * ‖B i‖ +
        ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i))))
    (hInput : Summable (fun i : ι =>
      ‖c i‖ * (‖C i‖ * ‖D i‖ * traceNorm H (T i - V i))))
    (hCoeff : Summable (fun i : ι =>
      ‖c i - d i‖ * (‖C i‖ * ‖D i‖ * traceNorm H (V i)))) :
    ‖((∑' i : ι, c i • sandwich (T i) (A i) (B i)) :
         TraceClass H).1 -
      ((∑' i : ι, d i • sandwich (V i) (C i) (D i)) :
         TraceClass H).1‖ ≤
      (∑' i : ι, ‖c i‖ *
        ((‖A i - C i‖ * ‖B i‖ +
          ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i))) +
      (∑' i : ι, ‖c i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (T i - V i))) +
      (∑' i : ι, ‖c i - d i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (V i))) := by
  let X : TraceClass H :=
    ∑' i : ι, c i • sandwich (T i) (A i) (B i)
  let W : TraceClass H :=
    ∑' i : ι, d i • sandwich (V i) (C i) (D i)
  have hmain : traceNorm H (X - W) ≤
      (∑' i : ι, ‖c i‖ *
        ((‖A i - C i‖ * ‖B i‖ +
          ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i))) +
      (∑' i : ι, ‖c i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (T i - V i))) +
      (∑' i : ι, ‖c i - d i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (V i))) := by
    dsimp [X, W]
    exact traceNorm_joint_varying_sandwich_tsum_le_v007
      c d A B C D T V hAT hCT hCV hDV hMult hInput hCoeff
  change ‖X.1 - W.1‖ ≤ _
  have hambient : ‖X.1 - W.1‖ ≤ traceNorm H (X - W) := by
    simpa only [sub_operator, norm_eq_genuineTraceNorm] using
      operator_norm_le_trace_norm (X - W)
  exact hambient.trans hmain

#print axioms ProbabilisticTheory.TraceClass.operatorNorm_joint_varying_sandwich_tsum_le_v007

end ProbabilisticTheory.TraceClass
