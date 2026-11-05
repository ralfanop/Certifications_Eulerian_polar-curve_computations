import GegenbauerFock.PhyslibTraceClassCoisometricComplement

/-!
# V007 — split-kernel decomposition of true CFC Schatten S₁

For a bounded Hilbert-space coisometry U, let
E(T)=U†TU, R(T)=UTU†, P=E∘R and Q=id-P.

The independently certified continuous split R∘E=id and
complementary projector Q yield the exact Banach-space
decomposition T=P(T)+Q(T). Moreover R(Q(T))=0 and

  Q(T)=T iff R(T)=0;
  range(Q)=kernel(R);
  P∘Q=0.

This is the non-unital S₁ operator-ideal splitting, valid on
arbitrary complete complex Hilbert spaces. We make no false
claim that E is onto or that Q is necessarily contractive.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every genuine CFC S₁ operator splits into its coisometric range
component and complementary component. -/
theorem coisometric_traceClass_decompose_v007
    (U : H →L[ℂ] H) (T : TraceClass H) :
    coisometric_sandwich_projection_v007 U T +
        coisometric_complementaryProjection_v007 U T = T := by
  have h := congrArg
    (fun f : TraceClass H →L[ℂ] TraceClass H => f T)
    (coisometric_projection_add_complement_v007 U)
  simpa only [ContinuousLinearMap.add_apply,
    ContinuousLinearMap.id_apply] using h

/-- The complementary CFC trace-class component lies in the
kernel of the continuous retraction R(T)=UTU†. -/
theorem coisometric_retraction_complement_zero_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : TraceClass H) :
    sandwichContinuous U U.adjoint
      (coisometric_complementaryProjection_v007 U T) = 0 := by
  change sandwichContinuous U U.adjoint
      (T - coisometric_sandwich_projection_v007 U T) = 0
  rw [map_sub]
  change sandwichContinuous U U.adjoint T -
      sandwichContinuous U U.adjoint
        (sandwichContinuous U.adjoint U
          (sandwichContinuous U U.adjoint T)) = 0
  rw [coisometric_sandwich_split_apply_v007 U hUUstar
    (sandwichContinuous U U.adjoint T)]
  exact sub_self _

/-- The complementary projection fixes exactly the S₁ kernel of
the coisometric retraction. This holds without a norm constraint. -/
theorem coisometric_retraction_kernel_iff_complement_fixed_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : TraceClass H) :
    sandwichContinuous U U.adjoint T = 0 ↔
      coisometric_complementaryProjection_v007 U T = T := by
  constructor
  · intro hR
    have hP : coisometric_sandwich_projection_v007 U T = 0 := by
      change sandwichContinuous U.adjoint U
          (sandwichContinuous U U.adjoint T) = 0
      rw [hR]
      exact map_zero _
    change T - coisometric_sandwich_projection_v007 U T = T
    rw [hP]
    exact sub_zero _
  · intro hQ
    rw [← hQ]
    exact coisometric_retraction_complement_zero_v007 U hUUstar T

/-- Exact range-kernel characterization for the genuine trace-normed
S₁ splitting: image(Q)=kernel(R). -/
theorem coisometric_complement_range_iff_retraction_kernel_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : TraceClass H) :
    (∃ V : TraceClass H,
       coisometric_complementaryProjection_v007 U V = T) ↔
      sandwichContinuous U U.adjoint T = 0 := by
  constructor
  · rintro ⟨V, rfl⟩
    exact coisometric_retraction_complement_zero_v007 U hUUstar V
  · intro hR
    exact ⟨T,
      (coisometric_retraction_kernel_iff_complement_fixed_v007
        U hUUstar T).mp hR⟩

/-- The range projection annihilates the complementary summand;
this is the companion identity to the already certified Q∘P=0. -/
theorem coisometric_projection_comp_complement_zero_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    (coisometric_sandwich_projection_v007 U).comp
      (coisometric_complementaryProjection_v007 U) = 0 := by
  apply ContinuousLinearMap.ext
  intro T
  change sandwichContinuous U.adjoint U
      (sandwichContinuous U U.adjoint
        (coisometric_complementaryProjection_v007 U T)) = 0
  rw [coisometric_retraction_complement_zero_v007 U hUUstar T]
  exact map_zero _

#print axioms ProbabilisticTheory.TraceClass.coisometric_traceClass_decompose_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_complement_zero_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_kernel_iff_complement_fixed_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_range_iff_retraction_kernel_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_comp_complement_zero_v007

end ProbabilisticTheory.TraceClass
