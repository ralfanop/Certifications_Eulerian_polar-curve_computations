import GegenbauerFock.PhyslibTraceClassSandwichComposition

/-!
# V007 — stability of CFC Schatten S₁ bilateral ideal actions

For arbitrary bounded A,B,C,D and an arbitrary (possibly nonpositive)
CFC trace-class T, perturbing either left or right multiplier changes
the true S₁ action by no more than

  (‖A-C‖*‖B‖ + ‖C‖*‖B-D‖) * ‖T‖₁.

The same sharp first-order bound controls the operator norm of the
difference of the two continuous complex-linear Schatten S₁ actions.
This does not require finite rank, positivity, or a separate integral
model of the ultraspherical kernel.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Bilateral ideal perturbation identity on the actual proof-carrying
trace-class subtype, without positivity or commutativity. -/
theorem sandwich_multiplier_sub_identity
    (T : TraceClass H) (A B C D : H →L[ℂ] H) :
    sandwich T A B - sandwich T C D =
      sandwich T (A - C) B + sandwich T C (B - D) := by
  apply Subtype.ext
  simp only [sub_operator, add_operator, sandwich_operator]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- Joint Lipschitz bound in the two bounded multipliers, measured in
the genuine CFC Schatten-S₁ norm of the trace-class variable. -/
theorem sandwich_multiplier_sub_norm_le
    (T : TraceClass H) (A B C D : H →L[ℂ] H) :
    ‖sandwich T A B - sandwich T C D‖ ≤
      (‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖) * ‖T‖ := by
  have h₁ : ‖sandwich T (A - C) B‖ ≤
      (‖A - C‖ * ‖B‖) * ‖T‖ := by
    calc
      ‖sandwich T (A - C) B‖ =
          ‖sandwichContinuous (A - C) B T‖ := rfl
      _ ≤ ‖sandwichContinuous (A - C) B‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖A - C‖ * ‖B‖) * ‖T‖ :=
        mul_le_mul_of_nonneg_right
          (sandwichContinuous_norm_le (A - C) B) (norm_nonneg _)
  have h₂ : ‖sandwich T C (B - D)‖ ≤
      (‖C‖ * ‖B - D‖) * ‖T‖ := by
    calc
      ‖sandwich T C (B - D)‖ =
          ‖sandwichContinuous C (B - D) T‖ := rfl
      _ ≤ ‖sandwichContinuous C (B - D)‖ * ‖T‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖C‖ * ‖B - D‖) * ‖T‖ :=
        mul_le_mul_of_nonneg_right
          (sandwichContinuous_norm_le C (B - D)) (norm_nonneg _)
  calc
    ‖sandwich T A B - sandwich T C D‖ =
        ‖sandwich T (A - C) B + sandwich T C (B - D)‖ := by
          rw [sandwich_multiplier_sub_identity]
    _ ≤ ‖sandwich T (A - C) B‖ + ‖sandwich T C (B - D)‖ :=
      norm_add_le _ _
    _ ≤ (‖A - C‖ * ‖B‖) * ‖T‖ +
          (‖C‖ * ‖B - D‖) * ‖T‖ :=
      add_le_add h₁ h₂
    _ = (‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖) * ‖T‖ := by
      ring

/-- Joint perturbation estimate for the actual CFC trace norm, not
for the weaker ambient bounded-operator norm. -/
theorem sandwich_multiplier_traceNorm_le
    (T : TraceClass H) (A B C D : H →L[ℂ] H) :
    traceNorm H (sandwich T A B - sandwich T C D) ≤
      (‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖) * traceNorm H T := by
  simpa only [norm_eq_genuineTraceNorm] using
    (sandwich_multiplier_sub_norm_le T A B C D)

/-- Bound in the Banach algebra of continuous linear operators on
the true Schatten S₁ Banach space. -/
theorem sandwichContinuous_multiplier_sub_norm_le
    (A B C D : H →L[ℂ] H) :
    ‖sandwichContinuous A B - sandwichContinuous C D‖ ≤
      ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (add_nonneg
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  intro T
  rw [ContinuousLinearMap.sub_apply,
    sandwichContinuous_apply, sandwichContinuous_apply]
  exact sandwich_multiplier_sub_norm_le T A B C D

#print axioms ProbabilisticTheory.TraceClass.sandwich_multiplier_sub_identity
#print axioms ProbabilisticTheory.TraceClass.sandwich_multiplier_sub_norm_le
#print axioms ProbabilisticTheory.TraceClass.sandwich_multiplier_traceNorm_le
#print axioms ProbabilisticTheory.TraceClass.sandwichContinuous_multiplier_sub_norm_le

end ProbabilisticTheory.TraceClass
