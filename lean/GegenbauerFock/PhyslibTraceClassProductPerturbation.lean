import GegenbauerFock.PhyslibTraceClassProductDistributivity

/-!
# V007 — two-input perturbation estimate in the true CFC trace norm

Boundedness, bilinearity, and submultiplicativity of genuine trace-class
composition imply the familiar difference estimate

  ‖T·V - S·W‖₁ ≤ ‖T-S‖₁ ‖V‖₁ + ‖S‖₁ ‖V-W‖₁.

This holds on complete complex Hilbert spaces of any dimension, for
nonpositive and nonnormal operators, without a trace-class unit.
It is a quantitative prerequisite for continuity of multiplication
in the (nonunital) Banach algebra.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact telescoping identity for the difference of two genuine
CFC Schatten-S₁ operator products. -/
theorem product_sub_product (T V S W : TraceClass H) :
    product T V - product S W =
      product (T - S) V + product S (V - W) := by
  apply Subtype.ext
  change T.1 * V.1 - S.1 * W.1 =
    (T.1 - S.1) * V.1 + S.1 * (V.1 - W.1)
  rw [sub_mul, mul_sub]
  abel

/-- Joint perturbation estimate for noncommuting actual CFC
trace-class operator products. -/
theorem norm_product_sub_le (T V S W : TraceClass H) :
    ‖product T V - product S W‖ ≤
      ‖T - S‖ * ‖V‖ + ‖S‖ * ‖V - W‖ := by
  calc
    ‖product T V - product S W‖ =
      ‖product (T - S) V + product S (V - W)‖ :=
        congrArg norm (product_sub_product T V S W)
    _ ≤ ‖product (T - S) V‖ + ‖product S (V - W)‖ :=
      norm_add_le _ _
    _ ≤ ‖T - S‖ * ‖V‖ + ‖S‖ * ‖V - W‖ :=
      add_le_add (norm_product_le _ _) (norm_product_le _ _)

#print axioms ProbabilisticTheory.TraceClass.product_sub_product
#print axioms ProbabilisticTheory.TraceClass.norm_product_sub_le

end ProbabilisticTheory.TraceClass
