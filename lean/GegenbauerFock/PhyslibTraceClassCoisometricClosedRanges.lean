import GegenbauerFock.PhyslibTraceClassCoisometricDecomposition

/-!
# V007 — closed range/kernel splitting in the true CFC S₁ Banach topology

For any coisometry U on a complete complex Hilbert space,
E(T)=U†TU and R(T)=UTU† act on the *genuine* CFC Schatten-S₁
Banach space with R∘E=id.

The already certified projection P=E∘R and complement Q=id-P
show S₁=range(E) ⊕ ker(R). Here we certify both components as
closed subsets of the actual trace-norm topology. This supplies
the topological closed-complement portion of the splitting,
with no assumption of finite dimension, positive operators,
or surjectivity of E.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The range of the genuine coisometric trace-class embedding is
closed in the CFC trace-norm Banach topology, as the fixed-point
set of the certified continuous projection P. -/
theorem coisometric_embedding_range_closed_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    IsClosed (Set.range (sandwichContinuous U.adjoint U)) := by
  have hrange :
      Set.range (sandwichContinuous U.adjoint U) =
        {T : TraceClass H |
          coisometric_sandwich_projection_v007 U T = T} := by
    ext T
    simpa only [Set.mem_range, Set.mem_setOf_eq] using
      (coisometric_projection_fixed_iff_image_v007 U hUUstar T).symm
  rw [hrange]
  exact isClosed_eq
    (coisometric_sandwich_projection_v007 U).continuous continuous_id

/-- The kernel of the bounded CFC trace-class retraction R is
closed in the *actual* Schatten-S₁ norm topology. -/
theorem coisometric_retraction_kernel_closed_v007
    (U : H →L[ℂ] H) :
    IsClosed {T : TraceClass H |
      sandwichContinuous U U.adjoint T = 0} := by
  exact isClosed_eq (sandwichContinuous U U.adjoint).continuous continuous_const

/-- The range of Q is exactly ker(R), and hence is closed in the
true CFC trace-norm topology. -/
theorem coisometric_complement_range_closed_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    IsClosed (Set.range (coisometric_complementaryProjection_v007 U)) := by
  have hrange :
      Set.range (coisometric_complementaryProjection_v007 U) =
        {T : TraceClass H | sandwichContinuous U U.adjoint T = 0} := by
    ext T
    simpa only [Set.mem_range, Set.mem_setOf_eq] using
      (coisometric_complement_range_iff_retraction_kernel_v007
        U hUUstar T)
  rw [hrange]
  exact coisometric_retraction_kernel_closed_v007 U

/-- Quantitative stability of the two closed CFC Schatten-S₁
components: the range part is contractive and the complement is
at worst twice the input norm. -/
theorem coisometric_closed_components_norm_le_v007
    (U : H →L[ℂ] H) (hUnorm : ‖U‖ ≤ (1 : ℝ))
    (T : TraceClass H) :
    ‖coisometric_sandwich_projection_v007 U T‖ ≤ ‖T‖ ∧
    ‖coisometric_complementaryProjection_v007 U T‖ ≤ 2 * ‖T‖ := by
  constructor
  · calc
      ‖coisometric_sandwich_projection_v007 U T‖ ≤
          ‖coisometric_sandwich_projection_v007 U‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖T‖ := mul_le_mul_of_nonneg_right
        (coisometric_projection_norm_le_one_v007 U hUnorm) (norm_nonneg _)
      _ = ‖T‖ := one_mul _
  · calc
      ‖coisometric_complementaryProjection_v007 U T‖ ≤
          ‖coisometric_complementaryProjection_v007 U‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 2 * ‖T‖ := mul_le_mul_of_nonneg_right
        (coisometric_complement_norm_le_two_v007 U hUnorm) (norm_nonneg _)

#print axioms ProbabilisticTheory.TraceClass.coisometric_embedding_range_closed_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_retraction_kernel_closed_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_complement_range_closed_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_closed_components_norm_le_v007

end ProbabilisticTheory.TraceClass
