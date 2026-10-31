import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# V007 — composition and metric bounds for continuous S₁ ideal actions

For the *actual* CFC Schatten-S₁ Banach space and bounded operators
A,B,C,D on any complete complex Hilbert space, the continuous ideal
actions compose exactly:

  Φ(C,D) ∘ Φ(A,B) = Φ(C*A,B*D).

They are quantitatively Lipschitz in the S₁ trace-norm metric with
constant ‖A‖ ‖B‖. No finite-dimensionality or positivity is required.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Left/right multipliers compose as genuine continuous complex
linear maps on the CFC trace-class carrier. -/
theorem sandwichContinuous_comp
    (A B C D : H →L[ℂ] H) :
    (sandwichContinuous C D).comp (sandwichContinuous A B) =
      sandwichContinuous (C * A) (B * D) := by
  apply ContinuousLinearMap.ext
  intro T
  simpa only [ContinuousLinearMap.comp_apply, sandwichContinuous_apply] using
    (sandwich_compose T A B C D)

/-- The identity bilateral action is exactly the identity endomorphism
of the true trace-normed Schatten S₁ space. -/
theorem sandwichContinuous_one_one_eq_id :
    sandwichContinuous (1 : H →L[ℂ] H) 1 =
      ContinuousLinearMap.id ℂ (TraceClass H) := by
  apply ContinuousLinearMap.ext
  intro T
  simpa only [ContinuousLinearMap.id_apply] using
    (sandwichContinuous_one_one T)

/-- Quantitative trace-norm Lipschitz estimate of a bilateral S₁
action, for arbitrary non-selfadjoint trace-class inputs. -/
theorem sandwich_traceNorm_sub_le
    (A B : H →L[ℂ] H) (T V : TraceClass H) :
    traceNorm H (sandwich T A B - sandwich V A B) ≤
      ‖A‖ * ‖B‖ * traceNorm H (T - V) := by
  change ‖sandwich T A B - sandwich V A B‖ ≤
    (‖A‖ * ‖B‖) * ‖T - V‖
  calc
    ‖sandwich T A B - sandwich V A B‖ =
        ‖sandwichContinuous A B (T - V)‖ := by
      rw [map_sub, sandwichContinuous_apply, sandwichContinuous_apply]
    _ ≤ ‖sandwichContinuous A B‖ * ‖T - V‖ :=
      ContinuousLinearMap.le_opNorm (sandwichContinuous A B) (T - V)
    _ ≤ (‖A‖ * ‖B‖) * ‖T - V‖ :=
      mul_le_mul_of_nonneg_right
        (sandwichContinuous_norm_le A B) (norm_nonneg _)

/-- Equivalent metric bound, independent of the chosen trace-class
membership witnesses. -/
theorem sandwich_dist_le
    (A B : H →L[ℂ] H) (T V : TraceClass H) :
    dist (sandwich T A B) (sandwich V A B) ≤
      ‖A‖ * ‖B‖ * dist T V := by
  simpa only [dist_eq_norm, norm_eq_genuineTraceNorm] using
    (sandwich_traceNorm_sub_le A B T V)

#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_comp
#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_one_one_eq_id
#print axioms ProbabilisticTheory.TraceClass.sandwich_traceNorm_sub_le
#print axioms ProbabilisticTheory.TraceClass.sandwich_dist_le

end ProbabilisticTheory.TraceClass
