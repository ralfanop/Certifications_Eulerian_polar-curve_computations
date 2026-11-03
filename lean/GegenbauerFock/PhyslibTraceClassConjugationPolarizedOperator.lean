import GegenbauerFock.PhyslibTraceClassConjugationPolarized

/-!
# V007 — operator-norm polarization on the genuine Schatten S₁ space

Upgrade the polarized pointwise trace-norm bound to the operator norm of
the induced bounded endomorphisms of S₁(H), and deduce exact invariance
under a global sign reversal U ↦ -U.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Full operator-norm polarized stability of the true Schatten S₁
conjugation action; not merely a bound for an individual test operator. -/
theorem conjugationContinuous_polarized_norm_le_v007
    (U V : H →L[ℂ] H) :
    ‖sandwichContinuous U.adjoint U -
      sandwichContinuous V.adjoint V‖ ≤
      ‖U - V‖ * ‖U + V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro T
  rw [ContinuousLinearMap.sub_apply]
  change ‖conjugate T U - conjugate T V‖ ≤
    (‖U - V‖ * ‖U + V‖) * ‖T‖
  have h := conjugation_traceNorm_polarized_le_v007 T U V
  change ‖conjugate T U - conjugate T V‖ ≤
    ‖U - V‖ * ‖U + V‖ * ‖T‖ at h
  simpa only [mul_assoc] using h

/-- Conjugation as an operator on S₁ is exactly invariant under
U ↦ -U, a cancellation not detected by the ordinary Lipschitz bound. -/
theorem conjugationContinuous_neg_invariant_v007
    (U : H →L[ℂ] H) :
    sandwichContinuous U.adjoint U =
      sandwichContinuous (-U).adjoint (-U) := by
  have h := conjugationContinuous_polarized_norm_le_v007 U (-U)
  have hZero :
      ‖sandwichContinuous U.adjoint U -
        sandwichContinuous (-U).adjoint (-U)‖ = 0 := by
    apply le_antisymm
    · simpa only [add_neg_cancel, norm_zero, mul_zero] using h
    · exact norm_nonneg _
  exact sub_eq_zero.mp (norm_eq_zero.mp hZero)

#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_polarized_norm_le_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_neg_invariant_v007

end ProbabilisticTheory.TraceClass
