import GegenbauerFock.PhyslibTraceClassSubmultiplicative

/-!
# V007 — algebraic distributivity of true CFC trace-class composition

The proof-carrying Schatten S₁ subtype is closed under multiplication
of bounded endomorphisms. Since this multiplication is exactly
bounded-operator composition, it distributes on both sides over the
already certified arbitrary additive S₁ structure. It also
commutes with complex scalar multiplication.

These results are the algebraic prerequisites for nonunital Banach
algebra structure. We do not install an unverified algebra typeclass
or assume the identity is trace class.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Left composition distributes over arbitrary S₁ sums. -/
theorem product_add (T V W : TraceClass H) :
    product T (V + W) = product T V + product T W := by
  apply Subtype.ext
  change T.1 * (V.1 + W.1) = T.1 * V.1 + T.1 * W.1
  exact mul_add _ _ _

/-- Right composition distributes over arbitrary S₁ sums. -/
theorem add_product (T V W : TraceClass H) :
    product (T + V) W = product T W + product V W := by
  apply Subtype.ext
  change (T.1 + V.1) * W.1 = T.1 * W.1 + V.1 * W.1
  exact add_mul _ _ _

/-- Multiplication on the left by the zero S₁ element. -/
@[simp] theorem zero_product (T : TraceClass H) :
    product 0 T = 0 := by
  apply Subtype.ext
  change (0 : H →L[ℂ] H) * T.1 = 0
  exact zero_mul T.1

/-- Multiplication on the right by the zero S₁ element. -/
@[simp] theorem product_zero (T : TraceClass H) :
    product T 0 = 0 := by
  apply Subtype.ext
  change T.1 * (0 : H →L[ℂ] H) = 0
  exact mul_zero T.1

/-- A scalar multiplying the first CFC trace-class factor can be
extracted from the composed operator. -/
theorem smul_product (c : ℂ) (T V : TraceClass H) :
    product (c • T) V = c • product T V := by
  apply Subtype.ext
  change (c • T.1) * V.1 = c • (T.1 * V.1)
  exact smul_mul_assoc c T.1 V.1

/-- Scalar multiplication in the second factor commutes with the
actual complex-linear CFC Schatten-S₁ composition. -/
theorem product_smul (c : ℂ) (T V : TraceClass H) :
    product T (c • V) = c • product T V := by
  apply Subtype.ext
  change T.1 * (c • V.1) = c • (T.1 * V.1)
  exact mul_smul_comm c T.1 V.1

#print axioms ProbabilisticTheory.TraceClass.product_add
#print axioms ProbabilisticTheory.TraceClass.add_product
#print axioms ProbabilisticTheory.TraceClass.zero_product
#print axioms ProbabilisticTheory.TraceClass.product_zero
#print axioms ProbabilisticTheory.TraceClass.smul_product
#print axioms ProbabilisticTheory.TraceClass.product_smul

end ProbabilisticTheory.TraceClass
