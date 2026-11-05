import GegenbauerFock.PhyslibTraceClassProductPerturbation
import GegenbauerFock.PhyslibTraceClassComplete
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# V007 — actual non-unital Banach ring structure of CFC trace class

The true proof-carrying Schatten S₁ carrier, with Mathlib's complex
normed-space structure and its CFC absolute trace norm, is a
non-unital normed ring under the actual composition of bounded maps.
The S₁ type does not in general contain the ambient identity in
infinite dimension: hence we deliberately use NonUnitalNormedRing,
never NormedRing or an assumed trace-class identity.

All operations, distributivities, associativity, sharp
submultiplicativity and completeness were separately certified
in the imported Lean modules. This candidate packages those exact
results into the pinned Mathlib typeclasses.
-/

noncomputable section
namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A genuine (possibly noncommutative) non-unital ring of CFC-trace
class maps under the true bounded-operator composition. -/
noncomputable instance instGenuineNonUnitalRing :
    NonUnitalRing (TraceClass H) where
  __ := (inferInstance : AddCommGroup (TraceClass H))
  mul := product
  mul_assoc := product_assoc
  left_distrib := product_add
  right_distrib := add_product
  zero_mul := zero_product
  mul_zero := product_zero

/-- The *actual* CFC trace norm defines a submultiplicative normed
ring, not a surrogate induced by the bounded-operator norm. -/
noncomputable instance instGenuineNonUnitalNormedRing :
    NonUnitalNormedRing (TraceClass H) where
  __ := instGenuineNonUnitalRing
  __ := (inferInstance : NormedAddCommGroup (TraceClass H))
  norm_mul_le := norm_product_le

/-- Banach completeness holds in the non-unital trace-class normed ring. -/
theorem instGenuineNonUnitalBanachRing_complete :
    CompleteSpace (TraceClass H) := inferInstance

#print axioms ProbabilisticTheory.TraceClass.instGenuineNonUnitalRing
#print axioms ProbabilisticTheory.TraceClass.instGenuineNonUnitalNormedRing
#print axioms ProbabilisticTheory.TraceClass.instGenuineNonUnitalBanachRing_complete

end ProbabilisticTheory.TraceClass
