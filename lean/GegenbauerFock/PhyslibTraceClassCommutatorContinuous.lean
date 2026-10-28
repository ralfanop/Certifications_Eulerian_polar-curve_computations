import GegenbauerFock.PhyslibTraceClassSandwichContinuous

/-!
# V007 — the bounded commutator derivation on the genuine Schatten S₁ norm

The map ad_A : T ↦ A*T - T*A is a bounded complex-linear endomorphism
of the true Physlib-compatible CFC trace-normed trace-class carrier.

The sharp universal operator-norm estimate ‖ad_A‖ ≤ 2‖A‖ holds on
arbitrary complete complex Hilbert spaces, without a positivity or
finite-dimensionality assumption. The bound also holds if H = 0.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual continuous complex-linear commutator on the Schatten S₁
space, not merely an algebraic closure assertion. -/
noncomputable def commutatorContinuous (A : H →L[ℂ] H) :
    TraceClass H →L[ℂ] TraceClass H :=
  sandwichContinuous A 1 - sandwichContinuous 1 A

/-- The continuous derivation really computes A*T - T*A on the
underlying bounded complex Hilbert operator. -/
@[simp] theorem commutatorContinuous_operator
    (A : H →L[ℂ] H) (T : TraceClass H) :
    (commutatorContinuous A T).1 = A * T.1 - T.1 * A := by
  simp only [commutatorContinuous, ContinuousLinearMap.sub_apply,
    sub_operator, sandwichContinuous_apply, sandwich_operator,
    mul_one, one_mul]

/-- The commutator is bounded in the actual CFC S₁ operator norm by
twice the ambient bounded-operator norm. -/
theorem commutatorContinuous_norm_le (A : H →L[ℂ] H) :
    ‖commutatorContinuous A‖ ≤ 2 * ‖A‖ := by
  have hOne : ‖(1 : H →L[ℂ] H)‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp
  have hL : ‖sandwichContinuous A 1‖ ≤ ‖A‖ := by
    calc
      ‖sandwichContinuous A 1‖ ≤ ‖A‖ * ‖(1 : H →L[ℂ] H)‖ :=
        sandwichContinuous_norm_le A 1
      _ ≤ ‖A‖ * 1 :=
        mul_le_mul_of_nonneg_left hOne (norm_nonneg A)
      _ = ‖A‖ := mul_one _
  have hR : ‖sandwichContinuous 1 A‖ ≤ ‖A‖ := by
    calc
      ‖sandwichContinuous 1 A‖ ≤ ‖(1 : H →L[ℂ] H)‖ * ‖A‖ :=
        sandwichContinuous_norm_le 1 A
      _ ≤ 1 * ‖A‖ :=
        mul_le_mul_of_nonneg_right hOne (norm_nonneg A)
      _ = ‖A‖ := one_mul _
  calc
    ‖commutatorContinuous A‖ ≤
        ‖sandwichContinuous A 1‖ + ‖sandwichContinuous 1 A‖ := by
      unfold commutatorContinuous
      exact norm_sub_le _ _
    _ ≤ ‖A‖ + ‖A‖ := add_le_add hL hR
    _ = 2 * ‖A‖ := by ring

/-- Trace-norm estimate for the continuous commutator applied to any
nonpositive or nonnormal class-trace operator. -/
theorem commutatorContinuous_traceNorm_le
    (A : H →L[ℂ] H) (T : TraceClass H) :
    traceNorm H (commutatorContinuous A T) ≤
      (2 * ‖A‖) * traceNorm H T := by
  change ‖commutatorContinuous A T‖ ≤ (2 * ‖A‖) * ‖T‖
  calc
    ‖commutatorContinuous A T‖ ≤
        ‖commutatorContinuous A‖ * ‖T‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ (2 * ‖A‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right
        (commutatorContinuous_norm_le A) (norm_nonneg _)

/-- The same Lipschitz estimate for the commutator as an S₁-valued
function of its trace-class input. -/
theorem commutatorContinuous_dist_le
    (A : H →L[ℂ] H) (T V : TraceClass H) :
    dist (commutatorContinuous A T)
         (commutatorContinuous A V) ≤
      (2 * ‖A‖) * dist T V := by
  simpa only [dist_eq_norm, map_sub] using
    (commutatorContinuous_traceNorm_le A (T - V))

#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_operator
#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_norm_le
#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_traceNorm_le
#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_dist_le

end ProbabilisticTheory.TraceClass
