import GegenbauerFock.PhyslibTraceClassConjugationPerturbation

/-!
# V007 — polarized Schatten S₁ conjugation perturbation

The symmetric polarization identity improves the ordinary Lipschitz
bound, and vanishes identically for V = -U:

  ‖U† T U - V† T V‖₁ ≤ ‖U - V‖ ‖U + V‖ ‖T‖₁.

Unlike the triangle estimate with (‖U‖ + ‖V‖), this bound detects
the exact phase symmetry U ↦ -U of the conjugation action.
All expressions use the genuine CFC trace-class subtype, without
positivity, selfadjointness, or coisometry assumptions.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Polarization, with no scalar-division coercions: the two bilateral
terms add to twice the difference of the two conjugations. -/
theorem conjugation_polarized_double_identity_v007
    (T : TraceClass H) (U V : H →L[ℂ] H) :
    sandwich T (U.adjoint - V.adjoint) (U + V) +
      sandwich T (U.adjoint + V.adjoint) (U - V) =
    (conjugate T U - conjugate T V) +
      (conjugate T U - conjugate T V) := by
  apply Subtype.ext
  simp only [add_operator, sub_operator, sandwich_operator, conjugate_operator]
  simp only [mul_assoc, mul_add, mul_sub, add_mul, sub_mul]
  abel

/-- Improved polarized trace-norm estimate on true Schatten S₁.
It is stronger than the general (‖U‖ + ‖V‖) estimate by the
triangle inequality ‖U+V‖ ≤ ‖U‖+‖V‖. -/
theorem conjugation_traceNorm_polarized_le_v007
    (T : TraceClass H) (U V : H →L[ℂ] H) :
    traceNorm H (conjugate T U - conjugate T V) ≤
      ‖U - V‖ * ‖U + V‖ * traceNorm H T := by
  change ‖conjugate T U - conjugate T V‖ ≤
    ‖U - V‖ * ‖U + V‖ * ‖T‖
  have hAdjPlus : ‖U.adjoint + V.adjoint‖ = ‖U + V‖ := by
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint]
    rw [← star_add, norm_star]
  have hLeft :
      ‖sandwich T (U.adjoint - V.adjoint) (U + V)‖ ≤
        ‖U - V‖ * ‖U + V‖ * ‖T‖ := by
    calc
      ‖sandwich T (U.adjoint - V.adjoint) (U + V)‖ =
          ‖sandwichContinuous (U.adjoint - V.adjoint) (U + V) T‖ := rfl
      _ ≤ ‖sandwichContinuous (U.adjoint - V.adjoint) (U + V)‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖U.adjoint - V.adjoint‖ * ‖U + V‖) * ‖T‖ :=
        mul_le_mul_of_nonneg_right
          (sandwichContinuous_norm_le (U.adjoint - V.adjoint) (U + V))
          (norm_nonneg _)
      _ = ‖U - V‖ * ‖U + V‖ * ‖T‖ := by
        rw [conjugation_adjoint_sub_norm_eq_v007 U V]
  have hRight :
      ‖sandwich T (U.adjoint + V.adjoint) (U - V)‖ ≤
        ‖U - V‖ * ‖U + V‖ * ‖T‖ := by
    calc
      ‖sandwich T (U.adjoint + V.adjoint) (U - V)‖ =
          ‖sandwichContinuous (U.adjoint + V.adjoint) (U - V) T‖ := rfl
      _ ≤ ‖sandwichContinuous (U.adjoint + V.adjoint) (U - V)‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖U.adjoint + V.adjoint‖ * ‖U - V‖) * ‖T‖ :=
        mul_le_mul_of_nonneg_right
          (sandwichContinuous_norm_le (U.adjoint + V.adjoint) (U - V))
          (norm_nonneg _)
      _ = ‖U - V‖ * ‖U + V‖ * ‖T‖ := by
        rw [hAdjPlus]
        ring
  let D : TraceClass H := conjugate T U - conjugate T V
  have hDouble : ‖D + D‖ = 2 * ‖D‖ := by
    calc
      ‖D + D‖ = ‖(2 : ℂ) • D‖ := by simp only [two_smul]
      _ = 2 * ‖D‖ := by simp
  have hTwo :
      2 * ‖D‖ ≤ 2 * (‖U - V‖ * ‖U + V‖ * ‖T‖) := by
    calc
      2 * ‖D‖ = ‖D + D‖ := hDouble.symm
      _ = ‖sandwich T (U.adjoint - V.adjoint) (U + V) +
          sandwich T (U.adjoint + V.adjoint) (U - V)‖ := by
            dsimp [D]
            rw [conjugation_polarized_double_identity_v007 T U V]
      _ ≤ ‖sandwich T (U.adjoint - V.adjoint) (U + V)‖ +
          ‖sandwich T (U.adjoint + V.adjoint) (U - V)‖ :=
        norm_add_le _ _
      _ ≤ (‖U - V‖ * ‖U + V‖ * ‖T‖) +
          (‖U - V‖ * ‖U + V‖ * ‖T‖) :=
        add_le_add hLeft hRight
      _ = 2 * (‖U - V‖ * ‖U + V‖ * ‖T‖) := by ring
  dsimp [D] at hTwo
  nlinarith

#print axioms ProbabilisticTheory.TraceClass.conjugation_polarized_double_identity_v007
#print axioms ProbabilisticTheory.TraceClass.conjugation_traceNorm_polarized_le_v007

end ProbabilisticTheory.TraceClass
