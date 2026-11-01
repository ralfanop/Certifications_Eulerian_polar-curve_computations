import GegenbauerFock.PhyslibTraceClassSandwichMultiplierStability

/-!
# V007 — Lipschitz dependence of arbitrary CFC S₁ conjugation on its multiplier

For bounded complex Hilbert operators U,V and every (possibly
nonselfadjoint) trace-class T, the true Schatten S₁ conjugation
T ↦ U† T U depends quantitatively on U, with

 ‖Phi_U - Phi_V‖_(B(S₁)) ≤ (‖U‖ + ‖V‖) ‖U-V‖,
 ‖U†TU - V†TV‖₁ ≤ (‖U‖ + ‖V‖) ‖U-V‖ ‖T‖₁.

The result holds without assuming U or V is a coisometry and
therefore also controls perturbations of the coisometric embeddings
previously certified. This makes no claim that a perturbed
operator remains a coisometry.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Adjoint subtraction is isometric for bounded operators on a
complete complex Hilbert space. -/
theorem conjugation_adjoint_sub_norm_eq_v007
    (U V : H →L[ℂ] H) :
    ‖U.adjoint - V.adjoint‖ = ‖U - V‖ := by
  rw [← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint]
  rw [← star_sub, norm_star]

/-- Sharp first-order Lipschitz dependence, in the operator norm
of continuous complex-linear maps on the actual CFC S₁ space. -/
theorem conjugationContinuous_multiplier_dist_le_v007
    (U V : H →L[ℂ] H) :
    ‖sandwichContinuous U.adjoint U -
      sandwichContinuous V.adjoint V‖ ≤
      (‖U‖ + ‖V‖) * ‖U - V‖ := by
  have hAdjNorm : ‖V.adjoint‖ = ‖V‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact norm_star V
  calc
    ‖sandwichContinuous U.adjoint U -
        sandwichContinuous V.adjoint V‖ ≤
      ‖U.adjoint - V.adjoint‖ * ‖U‖ +
        ‖V.adjoint‖ * ‖U - V‖ :=
      sandwichContinuous_multiplier_sub_norm_le U.adjoint U V.adjoint V
    _ = (‖U‖ + ‖V‖) * ‖U - V‖ := by
      rw [conjugation_adjoint_sub_norm_eq_v007 U V, hAdjNorm]
      ring

/-- Actual Schatten trace-norm perturbation of an arbitrary
possibly nonnormal or nonpositive CFC trace-class operator. -/
theorem conjugation_traceNorm_multiplier_dist_le_v007
    (U V : H →L[ℂ] H) (T : TraceClass H) :
    traceNorm H (conjugate T U - conjugate T V) ≤
      (‖U‖ + ‖V‖) * ‖U - V‖ * traceNorm H T := by
  change ‖conjugate T U - conjugate T V‖ ≤
    (‖U‖ + ‖V‖) * ‖U - V‖ * ‖T‖
  calc
    ‖conjugate T U - conjugate T V‖ =
        ‖(sandwichContinuous U.adjoint U -
          sandwichContinuous V.adjoint V) T‖ := by
      rw [ContinuousLinearMap.sub_apply]
      change ‖sandwich T U.adjoint U - sandwich T V.adjoint V‖ =
        ‖sandwich T U.adjoint U - sandwich T V.adjoint V‖
      rfl
    _ ≤ ‖sandwichContinuous U.adjoint U -
          sandwichContinuous V.adjoint V‖ * ‖T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ((‖U‖ + ‖V‖) * ‖U - V‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right
        (conjugationContinuous_multiplier_dist_le_v007 U V) (norm_nonneg _)
    _ = (‖U‖ + ‖V‖) * ‖U - V‖ * ‖T‖ := by ring

/-- For contractive multipliers the two trace-class conjugations
are 2-Lipschitz in the ambient bounded-operator norm. -/
theorem conjugationContinuous_contractions_dist_le_v007
    (U V : H →L[ℂ] H)
    (hU : ‖U‖ ≤ (1 : ℝ))
    (hV : ‖V‖ ≤ (1 : ℝ)) :
    ‖sandwichContinuous U.adjoint U -
      sandwichContinuous V.adjoint V‖ ≤
      2 * ‖U - V‖ := by
  calc
    ‖sandwichContinuous U.adjoint U -
        sandwichContinuous V.adjoint V‖ ≤
        (‖U‖ + ‖V‖) * ‖U - V‖ :=
      conjugationContinuous_multiplier_dist_le_v007 U V
    _ ≤ 2 * ‖U - V‖ :=
      mul_le_mul_of_nonneg_right (by linarith : ‖U‖ + ‖V‖ ≤ 2)
        (norm_nonneg _)

/-- The pointwise S₁ perturbation inequality specializes to two
contractions, with the explicit sharp uniform coefficient two.
No positivity, normality, or coisometry assumption on T is needed. -/
theorem conjugation_traceNorm_contractions_dist_le_v007
    (U V : H →L[ℂ] H) (T : TraceClass H)
    (hU : ‖U‖ ≤ (1 : ℝ))
    (hV : ‖V‖ ≤ (1 : ℝ)) :
    traceNorm H (conjugate T U - conjugate T V) ≤
      2 * ‖U - V‖ * traceNorm H T := by
  change ‖conjugate T U - conjugate T V‖ ≤
    2 * ‖U - V‖ * ‖T‖
  calc
    ‖conjugate T U - conjugate T V‖ ≤
        (‖U‖ + ‖V‖) * ‖U - V‖ * ‖T‖ :=
      conjugation_traceNorm_multiplier_dist_le_v007 U V T
    _ ≤ 2 * ‖U - V‖ * ‖T‖ := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (by linarith : ‖U‖ + ‖V‖ ≤ 2) (norm_nonneg _)
      · exact norm_nonneg _

#print axioms ProbabilisticTheory.TraceClass.conjugation_adjoint_sub_norm_eq_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_multiplier_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.conjugation_traceNorm_multiplier_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.conjugationContinuous_contractions_dist_le_v007
#print axioms ProbabilisticTheory.TraceClass.conjugation_traceNorm_contractions_dist_le_v007

end ProbabilisticTheory.TraceClass
