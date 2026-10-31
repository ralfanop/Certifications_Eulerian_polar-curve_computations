import GegenbauerFock.PhyslibTraceClassComplexNonUnitalAlgebra
import GegenbauerFock.PhyslibTraceClassCommutatorContinuous

/-!
# V007 — bounded inner derivations of the genuine CFC S₁ Banach algebra

The exact trace-class operator product satisfies the Leibniz rule
ad_A(TV) = ad_A(T)V + T ad_A(V) for each bounded ambient A.
Norm estimates below use the true CFC trace norm; no trace-class
identity, positivity, finite rank or commutativity is assumed.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Leibniz rule for the genuine bounded complex-linear inner derivation. -/
theorem commutatorContinuous_product_leibniz
    (A : H →L[ℂ] H) (T V : TraceClass H) :
    commutatorContinuous A (product T V) =
      product (commutatorContinuous A T) V +
        product T (commutatorContinuous A V) := by
  apply Subtype.ext
  simp only [commutatorContinuous_operator, product_operator, add_operator]
  simp only [sub_mul, mul_sub, mul_assoc]
  abel

/-- The full Leibniz estimate in the true Schatten-S₁ norm. -/
theorem norm_commutator_product_le
    (A : H →L[ℂ] H) (T V : TraceClass H) :
    ‖commutatorContinuous A (product T V)‖ ≤
      ‖commutatorContinuous A T‖ * ‖V‖ +
        ‖T‖ * ‖commutatorContinuous A V‖ := by
  rw [commutatorContinuous_product_leibniz]
  calc
    ‖product (commutatorContinuous A T) V +
        product T (commutatorContinuous A V)‖ ≤
        ‖product (commutatorContinuous A T) V‖ +
          ‖product T (commutatorContinuous A V)‖ :=
      norm_add_le _ _
    _ ≤ ‖commutatorContinuous A T‖ * ‖V‖ +
        ‖T‖ * ‖commutatorContinuous A V‖ :=
      add_le_add (norm_product_le _ _) (norm_product_le _ _)

#print axioms ProbabilisticTheory.TraceClass.commutatorContinuous_product_leibniz
#print axioms ProbabilisticTheory.TraceClass.norm_commutator_product_le

end ProbabilisticTheory.TraceClass
