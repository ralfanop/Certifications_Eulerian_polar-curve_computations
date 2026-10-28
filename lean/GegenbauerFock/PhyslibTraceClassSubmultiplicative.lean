import GegenbauerFock.PhyslibTraceClassIdealNormSharp
import GegenbauerFock.PhyslibTraceClassNormedSpace

/-!
# V007 — true CFC Schatten-S₁ operator product and submultiplicativity

Arbitrary complex trace-class operators form a (generally nonunital)
normed operator algebra under composition. We first prove the
exact CFC trace-norm bound

  ‖T * V‖₁ ≤ ‖T‖₁ * ‖V‖₁.

This is deduced only from the already-certified sharp S₁ ideal
estimate and the true operator-norm domination theorem. A
nontrivial-Hilbert-space assumption is **not** needed: the
possibly-zero norm of the identity is bounded by 1, rather than
incorrectly replaced by 1.

The proof-carrying subtype product is strictly the underlying
composition of bounded operators. Its associativity is recorded
without asserting an unverified complete Banach-algebra typeclass.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem traceNorm_mul_le
    (T V : H →L[ℂ] H) (hT : IsTraceClass T)
    (hV : IsTraceClass V) :
    traceNorm (T * V) (isTraceClass_mul_right T hT V) ≤
      traceNorm T hT * traceNorm V hV := by
  have hId : ‖(1 : H →L[ℂ] H)‖ ≤ (1 : ℝ) := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro x
    simp
  have hVop : ‖V‖ ≤ traceNorm V hV :=
    operatorNorm_le_traceNorm_via_sqrt_abs V hV
  have hTnonneg : 0 ≤ traceNorm T hT :=
    traceNorm_nonneg T hT
  have hbase := traceNorm_twoSided_le T 1 V hT
  calc
    traceNorm (T * V) (isTraceClass_mul_right T hT V) ≤
        ‖(1 : H →L[ℂ] H)‖ * ‖V‖ * traceNorm T hT := by
      simpa only [one_mul] using hbase
    _ ≤ 1 * traceNorm V hV * traceNorm T hT := by
      apply mul_le_mul_of_nonneg_right _ hTnonneg
      exact mul_le_mul hId hVop (norm_nonneg _) (by norm_num)
    _ = traceNorm T hT * traceNorm V hV := by ring

namespace TraceClass

/-- The genuine CFC S₁ composition on proof-carrying trace-class
operators, retaining exact operator-composition semantics. -/
noncomputable def product (T V : TraceClass H) : TraceClass H :=
  ⟨T.1 * V.1, isTraceClass_mul_right T.1 T.2 V.1⟩

@[simp] theorem product_operator (T V : TraceClass H) :
    (product T V).1 = T.1 * V.1 := rfl

theorem product_assoc (T V W : TraceClass H) :
    product (product T V) W = product T (product V W) := by
  apply Subtype.ext
  change (T.1 * V.1) * W.1 = T.1 * (V.1 * W.1)
  exact mul_assoc _ _ _

/-- Genuine trace-norm submultiplicativity of the concrete S₁
composition (not the ambient bounded-operator norm). -/
theorem norm_product_le (T V : TraceClass H) :
    ‖product T V‖ ≤ ‖T‖ * ‖V‖ := by
  change ProbabilisticTheory.traceNorm (T.1 * V.1)
      (isTraceClass_mul_right T.1 T.2 V.1) ≤
    ProbabilisticTheory.traceNorm T.1 T.2 *
      ProbabilisticTheory.traceNorm V.1 V.2
  exact ProbabilisticTheory.traceNorm_mul_le T.1 V.1 T.2 V.2

#print axioms ProbabilisticTheory.TraceClass.product_operator
#print axioms ProbabilisticTheory.TraceClass.product_assoc
#print axioms ProbabilisticTheory.TraceClass.norm_product_le

end TraceClass

#print axioms ProbabilisticTheory.traceNorm_mul_le

end ProbabilisticTheory
