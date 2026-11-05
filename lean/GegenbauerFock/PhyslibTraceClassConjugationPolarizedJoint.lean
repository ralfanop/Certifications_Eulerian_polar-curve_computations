import GegenbauerFock.PhyslibTraceClassConjugationPolarized

/-!
# V007 — simultaneous trace-class input and polarized multiplier perturbation

For arbitrary trace-class T,S and bounded complex-Hilbert U,V, the
full two-source perturbation estimate has the improved sign-sensitive
multiplier coefficient ‖U-V‖ ‖U+V‖, instead of
(‖U‖+‖V‖) ‖U-V‖. No positivity or coisometry assumptions.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Joint source and multiplier S₁ estimate, with the polarized
factor that vanishes if V = -U. -/
theorem conjugation_traceNorm_polarized_joint_le_v007
    (U V : H →L[ℂ] H) (T S : TraceClass H) :
    traceNorm H (conjugate T U - conjugate S V) ≤
      ‖U‖ ^ 2 * traceNorm H (T - S) +
      ‖U - V‖ * ‖U + V‖ * traceNorm H S := by
  change ‖conjugate T U - conjugate S V‖ ≤
    ‖U‖ ^ 2 * ‖T - S‖ +
    ‖U - V‖ * ‖U + V‖ * ‖S‖
  have hAdj : ‖U.adjoint‖ = ‖U‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star U
  have hInput :
      ‖conjugate T U - conjugate S U‖ ≤
        ‖U‖ ^ 2 * ‖T - S‖ := by
    calc
      ‖conjugate T U - conjugate S U‖ =
          ‖sandwichContinuous U.adjoint U (T - S)‖ := by
        change ‖sandwichContinuous U.adjoint U T -
          sandwichContinuous U.adjoint U S‖ = _
        rw [map_sub]
      _ ≤ ‖sandwichContinuous U.adjoint U‖ * ‖T - S‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖U.adjoint‖ * ‖U‖) * ‖T - S‖ :=
        mul_le_mul_of_nonneg_right
          (sandwichContinuous_norm_le U.adjoint U) (norm_nonneg _)
      _ = ‖U‖ ^ 2 * ‖T - S‖ := by rw [hAdj]; ring
  have hMultiplier := conjugation_traceNorm_polarized_le_v007 S U V
  change ‖conjugate S U - conjugate S V‖ ≤
    ‖U - V‖ * ‖U + V‖ * ‖S‖ at hMultiplier
  have hSplit :
      conjugate T U - conjugate S V =
        (conjugate T U - conjugate S U) +
        (conjugate S U - conjugate S V) := by
    abel
  calc
    ‖conjugate T U - conjugate S V‖ =
        ‖(conjugate T U - conjugate S U) +
          (conjugate S U - conjugate S V)‖ :=
      congrArg norm hSplit
    _ ≤ ‖conjugate T U - conjugate S U‖ +
        ‖conjugate S U - conjugate S V‖ := norm_add_le _ _
    _ ≤ ‖U‖ ^ 2 * ‖T - S‖ +
        ‖U - V‖ * ‖U + V‖ * ‖S‖ :=
      add_le_add hInput hMultiplier

#print axioms ProbabilisticTheory.TraceClass.conjugation_traceNorm_polarized_joint_le_v007

end ProbabilisticTheory.TraceClass
