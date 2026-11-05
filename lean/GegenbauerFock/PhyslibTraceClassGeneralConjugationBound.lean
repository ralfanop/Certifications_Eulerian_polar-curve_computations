import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# V007 — the sharp CFC S₁ congruence estimate without positivity

Unlike earlier positive-cone conjugation estimates, these two
statements apply to every possibly non-selfadjoint trace-class
endomorphism. They use the actual continuous bilateral action on
the genuine complex normed Schatten S₁ subtype.

For all bounded B, the map T ↦ B† T B has trace-norm operator
bound ‖B‖², and every contraction B acts contractively on S₁.
No Banach-completeness assumption is needed in these inequalities.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- True CFC trace-norm conjugation inequality, for *any*
(nonpositive, nonnormal or non-selfadjoint) S₁ operator. -/
theorem conjugate_traceNorm_le_general_v007
    (T : TraceClass H) (B : H →L[ℂ] H) :
    traceNorm H (conjugate T B) ≤ ‖B‖ ^ 2 * traceNorm H T := by
  have hAdj : ‖B.adjoint‖ = ‖B‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star B
  change ‖conjugate T B‖ ≤ ‖B‖ ^ 2 * ‖T‖
  calc
    ‖conjugate T B‖ = ‖sandwichContinuous B.adjoint B T‖ := rfl
    _ ≤ ‖sandwichContinuous B.adjoint B‖ * ‖T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖B.adjoint‖ * ‖B‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right
        (sandwichContinuous_norm_le B.adjoint B) (norm_nonneg _)
    _ = ‖B‖ ^ 2 * ‖T‖ := by
      rw [hAdj]
      ring

/-- General (not necessarily positive) S₁ contractivity of
bounded-operator conjugation by a contraction B. -/
theorem conjugate_traceNorm_le_general_contraction_v007
    (T : TraceClass H) (B : H →L[ℂ] H)
    (hB : ‖B‖ ≤ 1) :
    traceNorm H (conjugate T B) ≤ traceNorm H T := by
  have hB2 : ‖B‖ ^ 2 ≤ (1 : ℝ) := by
    simpa only [one_pow] using
      ((sq_le_sq₀ (norm_nonneg _) zero_le_one).2 hB)
  calc
    traceNorm H (conjugate T B) ≤
        ‖B‖ ^ 2 * traceNorm H T :=
      conjugate_traceNorm_le_general_v007 T B
    _ ≤ (1 : ℝ) * traceNorm H T :=
      mul_le_mul_of_nonneg_right hB2 (norm_nonneg T)
    _ = traceNorm H T := one_mul _

#print axioms ProbabilisticTheory.TraceClass.conjugate_traceNorm_le_general_v007
#print axioms ProbabilisticTheory.TraceClass.conjugate_traceNorm_le_general_contraction_v007

end ProbabilisticTheory.TraceClass
