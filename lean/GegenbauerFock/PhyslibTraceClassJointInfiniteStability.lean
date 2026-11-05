import GegenbauerFock.PhyslibTraceClassVaryingSandwichStability
import GegenbauerFock.PhyslibTraceClassVaryingSandwichOperatorStability

/-!
# V007 — simultaneous three-axis Lipschitz stability of infinite CFC S₁ series

The coefficients cᵢ, bounded bilateral multipliers Aᵢ,Bᵢ, and the
trace-class input Tᵢ may ALL vary simultaneously. By inserting
two intermediate absolutely convergent series and using the three
independently kernel-certified trace-norm perturbation theorems,
we derive a global, coefficient-one estimate.

All sums and differences live in the genuine complex Schatten S₁
Banach topology; no positivity, finite rank, shared basis, or
commutation hypotheses are imposed.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A single genuine S₁ bound for simultaneous perturbations of
complex coefficients, bounded left/right multipliers, and arbitrary
(nonpositive, possibly nonnormal) trace-class inputs. -/
theorem traceNorm_joint_varying_sandwich_tsum_le_v007
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
    traceNorm H
      ((∑' i : ι, c i • sandwich (T i) (A i) (B i)) -
       (∑' i : ι, d i • sandwich (V i) (C i) (D i))) ≤
      (∑' i : ι, ‖c i‖ *
        ((‖A i - C i‖ * ‖B i‖ +
          ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i))) +
      (∑' i : ι, ‖c i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (T i - V i))) +
      (∑' i : ι, ‖c i - d i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (V i))) := by
  let X : TraceClass H :=
    ∑' i : ι, c i • sandwich (T i) (A i) (B i)
  let Y : TraceClass H :=
    ∑' i : ι, c i • sandwich (T i) (C i) (D i)
  let Z : TraceClass H :=
    ∑' i : ι, c i • sandwich (V i) (C i) (D i)
  let W : TraceClass H :=
    ∑' i : ι, d i • sandwich (V i) (C i) (D i)
  have h₁ : traceNorm H (X - Y) ≤
      ∑' i : ι, ‖c i‖ *
        ((‖A i - C i‖ * ‖B i‖ +
          ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i)) := by
    dsimp [X, Y]
    exact traceNorm_varying_sandwich_multiplier_tsum_sub_le_v007
      c A B C D T hAT hCT hMult
  have h₂ : traceNorm H (Y - Z) ≤
      ∑' i : ι, ‖c i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (T i - V i)) := by
    dsimp [Y, Z]
    exact traceNorm_varying_sandwich_input_tsum_sub_le_v007
      c C D T V hCT hCV hInput
  have h₃ : traceNorm H (Z - W) ≤
      ∑' i : ι, ‖c i - d i‖ *
        (‖C i‖ * ‖D i‖ * traceNorm H (V i)) := by
    dsimp [Z, W]
    exact traceNorm_varying_sandwich_coeff_tsum_sub_le_v007
      c d C D V hCV hDV hCoeff
  change traceNorm H (X - W) ≤ _
  calc
    traceNorm H (X - W) = ‖X - W‖ :=
      (norm_eq_genuineTraceNorm _).symm
    _ = ‖(X - Y) + (Y - Z) + (Z - W)‖ := by
      congr 1
      abel
    _ ≤ (‖X - Y‖ + ‖Y - Z‖) + ‖Z - W‖ := by
      calc
        ‖(X - Y) + (Y - Z) + (Z - W)‖ ≤
            ‖(X - Y) + (Y - Z)‖ + ‖Z - W‖ :=
          norm_add_le _ _
        _ ≤ (‖X - Y‖ + ‖Y - Z‖) + ‖Z - W‖ :=
          add_le_add (norm_add_le _ _) (le_refl _)
    _ = (traceNorm H (X - Y) + traceNorm H (Y - Z)) +
          traceNorm H (Z - W) := by
      simp only [norm_eq_genuineTraceNorm]
    _ ≤
        (∑' i : ι, ‖c i‖ *
          ((‖A i - C i‖ * ‖B i‖ +
            ‖C i‖ * ‖B i - D i‖) * traceNorm H (T i))) +
        (∑' i : ι, ‖c i‖ *
          (‖C i‖ * ‖D i‖ * traceNorm H (T i - V i))) +
        (∑' i : ι, ‖c i - d i‖ *
          (‖C i‖ * ‖D i‖ * traceNorm H (V i))) :=
      add_le_add (add_le_add h₁ h₂) h₃

#print axioms ProbabilisticTheory.TraceClass.traceNorm_joint_varying_sandwich_tsum_le_v007

end ProbabilisticTheory.TraceClass
