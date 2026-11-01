import GegenbauerFock.PhyslibTraceClassNonUnitalBanachRing

/-!
# V007 — complex scalar centrality for the non-unital CFC Schatten S₁ Banach algebra

The true CFC trace-class operator space is a normed complex Banach
space and a normed non-unital ring under operator composition.
For a non-unital algebra Mathlib uses Module and the two compatibility
typeclasses IsScalarTower and SMulCommClass rather than the unital
Algebra ℂ interface, whose scalar-unit map would incorrectly require
the identity to be trace class on every infinite-dimensional H.

This module packages the previously certified left and right
complex scalar compatibility of the real operator product as the
actual Mathlib scalar-centrality typeclasses.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The action of complex scalars is compatible with composition
when the scalar is attached to the first trace-class factor. -/
instance instGenuineS1ScalarTower :
    IsScalarTower ℂ (TraceClass H) (TraceClass H) where
  smul_assoc c T V := by
    apply Subtype.ext
    change (c • T.1) * V.1 = c • (T.1 * V.1)
    exact smul_mul_assoc c T.1 V.1

/-- Complex scalar multiplication is central for genuine CFC
trace-class multiplication: T·(c V) = c(T·V). -/
instance instGenuineS1ScalarCentrality :
    SMulCommClass ℂ (TraceClass H) (TraceClass H) where
  smul_comm c T V := by
    apply Subtype.ext
    change c • (T.1 * V.1) = T.1 * (c • V.1)
    exact (mul_smul_comm c T.1 V.1).symm

/-- Explicit verification of the non-unital complex Banach-algebra
interface, without an algebraMap or unit. -/
theorem genuineS1_scalar_mul_assoc
    (c : ℂ) (T V : TraceClass H) :
    product (c • T) V = c • product T V :=
  smul_product c T V

theorem genuineS1_mul_scalar_assoc
    (c : ℂ) (T V : TraceClass H) :
    product T (c • V) = c • product T V :=
  product_smul c T V

#print axioms ProbabilisticTheory.TraceClass.instGenuineS1ScalarTower
#print axioms ProbabilisticTheory.TraceClass.instGenuineS1ScalarCentrality
#print axioms ProbabilisticTheory.TraceClass.genuineS1_scalar_mul_assoc
#print axioms ProbabilisticTheory.TraceClass.genuineS1_mul_scalar_assoc

end ProbabilisticTheory.TraceClass
