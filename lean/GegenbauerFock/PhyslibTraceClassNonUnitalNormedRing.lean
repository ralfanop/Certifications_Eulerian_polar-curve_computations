import GegenbauerFock.PhyslibTraceClassComplete
import GegenbauerFock.PhyslibTraceClassProductDistributivity
import Mathlib.Analysis.Normed.Ring.Basic

/-!
# V007 — genuine nonunital normed-ring instance on CFC Schatten S₁

The genuine complex Schatten trace class is a complete normed space
in the CFC absolute trace norm. The previously certified composition
operation is associative and distributive, with sharp coefficient-one
norm submultiplicativity.

Here the same concrete product is installed as a **nonunital** normed
ring, so standard Mathlib ring/metric theorems can act on actual trace
class operators. There is intentionally NO claim that the identity
operator is trace class on an infinite-dimensional Hilbert space.
-/

noncomputable section

namespace ProbabilisticTheory.TraceClass

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual CFC trace-class operator algebra, with multiplication
given by bounded-operator composition. This is nonunital in general. -/
noncomputable instance instGenuineNonUnitalNormedRing :
    NonUnitalNormedRing (TraceClass H) where
  mul := product
  mul_assoc := product_assoc
  zero_mul := zero_product
  mul_zero := product_zero
  left_distrib := product_add
  right_distrib := add_product
  dist_eq := by
    intro T V
    calc
      dist T V = ‖T - V‖ := dist_eq_norm
      _ = ‖V - T‖ := norm_sub_rev _ _
      _ = ‖-T + V‖ := by rw [sub_eq_add_neg, add_comm]
  norm_mul_le := norm_product_le

/-- The installed ring multiplication is the genuine trace-class
composition, not ambient pointwise multiplication or a formal symbol. -/
theorem genuine_nonunital_mul_eq_product (T V : TraceClass H) :
    T * V = product T V := rfl

/-- The sharp genuine CFC norm estimate is now available through
ordinary algebraic multiplication notation. -/
theorem genuine_nonunital_norm_mul_le (T V : TraceClass H) :
    ‖T * V‖ ≤ ‖T‖ * ‖V‖ :=
  norm_mul_le T V

/-- The new normed-ring structure retains the separately certified
Banach completeness in the exact same CFC trace norm. -/
theorem genuine_nonunital_complete :
    CompleteSpace (TraceClass H) := inferInstance

#print axioms ProbabilisticTheory.TraceClass.genuine_nonunital_mul_eq_product
#print axioms ProbabilisticTheory.TraceClass.genuine_nonunital_norm_mul_le
#print axioms ProbabilisticTheory.TraceClass.genuine_nonunital_complete

end ProbabilisticTheory.TraceClass
