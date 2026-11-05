import GegenbauerFock.PhyslibTraceClassProductDistributivity

/-!
# V007 — continuous left and right Schatten S₁ Banach multipliers

For every genuine CFC trace-class element A, multiplication
V ↦ A*V and V ↦ V*A defines a bounded complex-linear endomorphism
of the complete trace-normed space S₁(H), and each multiplier has
continuous-linear-map operator norm at most ‖A‖₁.

The construction uses the kernel-certified CFC S₁ product bound
and its exact distributivity. We never assume that the identity
operator belongs to S₁, nor that H has finite dimension.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Left multiplication by any CFC S₁ operator, as a bounded
complex-linear endomorphism of the true trace-norm Banach space. -/
noncomputable def leftMultiplier (A : TraceClass H) :
    TraceClass H →L[ℂ] TraceClass H :=
  ({ toFun := fun V => product A V
     map_add' := by
       intro V W
       exact product_add A V W
     map_smul' := by
       intro c V
       exact product_smul c A V
    } : TraceClass H →ₗ[ℂ] TraceClass H).mkContinuous ‖A‖ (by
      intro V
      change ‖product A V‖ ≤ ‖A‖ * ‖V‖
      exact norm_product_le A V)

/-- Right multiplication by any CFC S₁ operator, as a bounded
complex-linear endomorphism of the true trace-norm Banach space. -/
noncomputable def rightMultiplier (A : TraceClass H) :
    TraceClass H →L[ℂ] TraceClass H :=
  ({ toFun := fun V => product V A
     map_add' := by
       intro V W
       exact add_product V W A
     map_smul' := by
       intro c V
       exact smul_product c V A
    } : TraceClass H →ₗ[ℂ] TraceClass H).mkContinuous ‖A‖ (by
      intro V
      change ‖product V A‖ ≤ ‖A‖ * ‖V‖
      calc
        ‖product V A‖ ≤ ‖V‖ * ‖A‖ := norm_product_le V A
        _ = ‖A‖ * ‖V‖ := mul_comm _ _)

@[simp] theorem leftMultiplier_apply (A V : TraceClass H) :
    leftMultiplier A V = product A V := rfl

@[simp] theorem rightMultiplier_apply (A V : TraceClass H) :
    rightMultiplier A V = product V A := rfl

/-- Sharp universal estimate without any S₁ unit assumption. -/
theorem norm_leftMultiplier_le (A : TraceClass H) :
    ‖leftMultiplier A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro V
  change ‖product A V‖ ≤ ‖A‖ * ‖V‖
  exact norm_product_le A V

/-- Sharp universal estimate for right multiplication. -/
theorem norm_rightMultiplier_le (A : TraceClass H) :
    ‖rightMultiplier A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro V
  change ‖product V A‖ ≤ ‖A‖ * ‖V‖
  calc
    ‖product V A‖ ≤ ‖V‖ * ‖A‖ := norm_product_le V A
    _ = ‖A‖ * ‖V‖ := mul_comm _ _

#print axioms ProbabilisticTheory.TraceClass.leftMultiplier_apply
#print axioms ProbabilisticTheory.TraceClass.rightMultiplier_apply
#print axioms ProbabilisticTheory.TraceClass.norm_leftMultiplier_le
#print axioms ProbabilisticTheory.TraceClass.norm_rightMultiplier_le

end ProbabilisticTheory.TraceClass
