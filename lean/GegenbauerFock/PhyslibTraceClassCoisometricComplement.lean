import GegenbauerFock.PhyslibTraceClassCoisometricProjection

/-!
# V007 — complementary projections in the true CFC Schatten S₁ norm

For a coisometry U with U*U†=1, the independently certified
bounded CFC-S₁ projection P=E∘R admits the continuous complement
Q=id-P. These are complementary idempotents:

  P+Q=id, Q∘P=0, Q∘Q=Q.

For a contractive coisometry, the certified bound ‖P‖≤1 yields
the safe universal bound ‖Q‖≤2. We do not assert that Q is a
contraction; such a claim is false for general contractive projections
on arbitrary Banach spaces.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The continuous linear complement of the coisometric range
projection in the genuine complex trace-normed S₁ space. -/
noncomputable def coisometric_complementaryProjection_v007
    (U : H →L[ℂ] H) : TraceClass H →L[ℂ] TraceClass H :=
  ContinuousLinearMap.id ℂ (TraceClass H) -
    coisometric_sandwich_projection_v007 U

/-- The range projection and its complement sum to the identity
as actual bounded complex-linear maps on the trace class. -/
theorem coisometric_projection_add_complement_v007
    (U : H →L[ℂ] H) :
    coisometric_sandwich_projection_v007 U +
        coisometric_complementaryProjection_v007 U =
      ContinuousLinearMap.id ℂ (TraceClass H) := by
  apply ContinuousLinearMap.ext
  intro T
  simp only [ContinuousLinearMap.add_apply,
    coisometric_complementaryProjection_v007,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
  abel

/-- The complementary projection annihilates the image of P.
Thus the two projections are complementary on the actual S₁ space. -/
theorem coisometric_complement_comp_projection_zero_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    (coisometric_complementaryProjection_v007 U).comp
      (coisometric_sandwich_projection_v007 U) = 0 := by
  apply ContinuousLinearMap.ext
  intro T
  have hp := congrArg
    (fun f : TraceClass H →L[ℂ] TraceClass H => f T)
    (coisometric_projection_idempotent_v007 U hUUstar)
  have hfix :
      coisometric_sandwich_projection_v007 U
        (coisometric_sandwich_projection_v007 U T) =
      coisometric_sandwich_projection_v007 U T := by
    simpa only [ContinuousLinearMap.comp_apply] using hp
  simp only [ContinuousLinearMap.comp_apply,
    coisometric_complementaryProjection_v007,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.zero_apply, hfix, sub_self]

/-- The complementary CFC-S₁ endomorphism is itself idempotent. -/
theorem coisometric_complement_idempotent_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    (coisometric_complementaryProjection_v007 U).comp
        (coisometric_complementaryProjection_v007 U) =
      coisometric_complementaryProjection_v007 U := by
  apply ContinuousLinearMap.ext
  intro T
  have hp := congrArg
    (fun f : TraceClass H →L[ℂ] TraceClass H => f T)
    (coisometric_projection_idempotent_v007 U hUUstar)
  have hfix :
      coisometric_sandwich_projection_v007 U
        (coisometric_sandwich_projection_v007 U T) =
      coisometric_sandwich_projection_v007 U T := by
    simpa only [ContinuousLinearMap.comp_apply] using hp
  simp only [ContinuousLinearMap.comp_apply,
    coisometric_complementaryProjection_v007,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_sub, hfix]
  abel

/-- A correct universal bound for the complement of a contractive
projection in the actual CFC Schatten S₁ operator norm. -/
theorem coisometric_complement_norm_le_two_v007
    (U : H →L[ℂ] H) (hUnorm : ‖U‖ ≤ (1 : ℝ)) :
    ‖coisometric_complementaryProjection_v007 U‖ ≤ 2 := by
  have hid :
      ‖ContinuousLinearMap.id ℂ (TraceClass H)‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro T
    simp
  have hp := coisometric_projection_norm_le_one_v007 U hUnorm
  calc
    ‖coisometric_complementaryProjection_v007 U‖ =
        ‖ContinuousLinearMap.id ℂ (TraceClass H) -
          coisometric_sandwich_projection_v007 U‖ := rfl
    _ ≤ ‖ContinuousLinearMap.id ℂ (TraceClass H)‖ +
        ‖coisometric_sandwich_projection_v007 U‖ :=
      norm_sub_le _ _
    _ ≤ (1 : ℝ) + 1 := add_le_add hid hp
    _ = 2 := by norm_num

#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_add_complement_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_comp_projection_zero_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_idempotent_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_norm_le_two_v007

end ProbabilisticTheory.TraceClass
