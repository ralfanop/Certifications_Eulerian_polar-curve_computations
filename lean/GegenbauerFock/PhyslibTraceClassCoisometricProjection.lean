import GegenbauerFock.PhyslibTraceClassCoisometricSplit
import GegenbauerFock.PhyslibTraceClassCoisometricEmbedding

/-!
# V007 — contractive projection onto the coisometric Schatten-S₁ image

Let U : H →L[ℂ] H be a coisometry on a complete complex Hilbert
space, U*U†=1. On the real CFC trace-normed complex Banach space
S₁(H), set E(T)=U†TU and R(T)=UTU†, and P=E∘R.

The independently certified split R∘E=id proves P²=P and
P(E(T))=E(T). Moreover, if ‖U‖≤1 then ‖P‖≤1. The range of
this bounded projection is exactly the image of E; no surjectivity
of E or identity element in S₁ is postulated.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- An actual bounded complex-linear idempotent on the CFC Schatten
S₁ class, induced by coisometric left/right conjugations. -/
noncomputable def coisometric_sandwich_projection_v007
    (U : H →L[ℂ] H) : TraceClass H →L[ℂ] TraceClass H :=
  (sandwichContinuous U.adjoint U).comp
    (sandwichContinuous U U.adjoint)

/-- The image of T ↦ U† T U is pointwise fixed by the projection. -/
theorem coisometric_projection_fixes_image_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : TraceClass H) :
    coisometric_sandwich_projection_v007 U
        (sandwichContinuous U.adjoint U T) =
      sandwichContinuous U.adjoint U T := by
  change sandwichContinuous U.adjoint U
      (sandwichContinuous U U.adjoint
        (sandwichContinuous U.adjoint U T)) =
    sandwichContinuous U.adjoint U T
  rw [coisometric_sandwich_split_apply_v007 U hUUstar T]

/-- This continuous operator is a genuine idempotent, with no
finite-rank or positivity hypothesis. -/
theorem coisometric_projection_idempotent_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1) :
    (coisometric_sandwich_projection_v007 U).comp
        (coisometric_sandwich_projection_v007 U) =
      coisometric_sandwich_projection_v007 U := by
  apply ContinuousLinearMap.ext
  intro T
  change sandwichContinuous U.adjoint U
      (sandwichContinuous U U.adjoint
        (sandwichContinuous U.adjoint U
          (sandwichContinuous U U.adjoint T))) =
    sandwichContinuous U.adjoint U
      (sandwichContinuous U U.adjoint T)
  rw [coisometric_sandwich_split_apply_v007 U hUUstar
    (sandwichContinuous U U.adjoint T)]

/-- A point belongs to the range of the coisometric embedding
precisely when it is fixed by the CFC Schatten-S₁ projection. -/
theorem coisometric_projection_fixed_iff_image_v007
    (U : H →L[ℂ] H) (hUUstar : U * U.adjoint = 1)
    (T : TraceClass H) :
    coisometric_sandwich_projection_v007 U T = T ↔
      ∃ S : TraceClass H, sandwichContinuous U.adjoint U S = T := by
  constructor
  · intro h
    refine ⟨sandwichContinuous U U.adjoint T, ?_⟩
    simpa only [coisometric_sandwich_projection_v007,
      ContinuousLinearMap.comp_apply] using h
  · rintro ⟨S, hS⟩
    rw [← hS]
    exact coisometric_projection_fixes_image_v007 U hUUstar S

/-- If the coisometry is contractive, the projection onto the
coisometric S₁ image is itself contractive in the *actual* CFC norm. -/
theorem coisometric_projection_norm_le_one_v007
    (U : H →L[ℂ] H) (hUnorm : ‖U‖ ≤ (1 : ℝ)) :
    ‖coisometric_sandwich_projection_v007 U‖ ≤ 1 := by
  have hAdjNorm : ‖U.adjoint‖ = ‖U‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star U
  have hsq : ‖U‖ * ‖U‖ ≤ (1 : ℝ) := by
    have hnonneg : 0 ≤ ‖U‖ := norm_nonneg U
    nlinarith [sq_nonneg (‖U‖ - 1)]
  have hE : ‖sandwichContinuous U.adjoint U‖ ≤ (1 : ℝ) := by
    calc
      ‖sandwichContinuous U.adjoint U‖ ≤ ‖U.adjoint‖ * ‖U‖ :=
        sandwichContinuous_norm_le U.adjoint U
      _ = ‖U‖ * ‖U‖ := by rw [hAdjNorm]
      _ ≤ 1 := hsq
  have hR : ‖sandwichContinuous U U.adjoint‖ ≤ (1 : ℝ) := by
    calc
      ‖sandwichContinuous U U.adjoint‖ ≤ ‖U‖ * ‖U.adjoint‖ :=
        sandwichContinuous_norm_le U U.adjoint
      _ = ‖U‖ * ‖U‖ := by rw [hAdjNorm]
      _ ≤ 1 := hsq
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro T
  change ‖sandwichContinuous U.adjoint U
      (sandwichContinuous U U.adjoint T)‖ ≤ 1 * ‖T‖
  calc
    ‖sandwichContinuous U.adjoint U
        (sandwichContinuous U U.adjoint T)‖ ≤
        ‖sandwichContinuous U.adjoint U‖ *
          ‖sandwichContinuous U U.adjoint T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖sandwichContinuous U U.adjoint T‖ :=
      mul_le_mul_of_nonneg_right hE (norm_nonneg _)
    _ = ‖sandwichContinuous U U.adjoint T‖ := one_mul _
    _ ≤ ‖sandwichContinuous U U.adjoint‖ * ‖T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖T‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)

#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_fixes_image_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_idempotent_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_fixed_iff_image_v007
#print axioms ProbabilisticTheory.TraceClass.coisometric_projection_norm_le_one_v007

end ProbabilisticTheory.TraceClass
