import GegenbauerFock.PhyslibGeneralHSProductTraceClass
import GegenbauerFock.PhyslibHilbertSchmidtAdditive

/-!
# V007 — trace-class sums sharing one Hilbert--Schmidt factor

The generic S₂*S₂ ⊆ S₁ product theorem and the already
certified additivity of Hilbert--Schmidt maps imply closure for
sums of trace-class products which share a genuine S₂ factor.

This is a useful model-independent intermediate step toward
general S₁ additivity.  We do *not* assert that arbitrary
trace-class T and U admit a common HS factor: that unrestricted
statement requires further analytic work. No extra axioms.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A pair of arbitrary HS products with a common left factor
has a genuine CFC trace-class sum. -/
theorem isTraceClass_add_common_left_HS
    (R S T : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    (hT : HilbertSchmidt.IsHilbertSchmidt T) :
    IsTraceClass (R * S + R * T) := by
  have hsum : HilbertSchmidt.IsHilbertSchmidt (S + T) :=
    HilbertSchmidt.isHilbertSchmidt_add hS hT
  have hp : IsTraceClass (R * (S + T)) :=
    isTraceClass_mul_of_twoHilbertSchmidt R (S + T) hR hsum
  simpa only [mul_add] using hp

/-- A pair of arbitrary HS products with a common right factor
has a genuine CFC trace-class sum. -/
theorem isTraceClass_add_common_right_HS
    (R S T : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    (hT : HilbertSchmidt.IsHilbertSchmidt T) :
    IsTraceClass (R * S + T * S) := by
  have hsum : HilbertSchmidt.IsHilbertSchmidt (R + T) :=
    HilbertSchmidt.isHilbertSchmidt_add hR hT
  have hp : IsTraceClass ((R + T) * S) :=
    isTraceClass_mul_of_twoHilbertSchmidt (R + T) S hsum hS
  simpa only [add_mul] using hp

/-- Finite sums of Hilbert--Schmidt endomorphisms remain S₂
without any dimension, rank, or common-witness-basis assumption. -/
theorem isHilbertSchmidt_finset_sum
    {ι : Type*} (s : Finset ι) (F : ι → H →L[ℂ] H)
    (hF : ∀ i, HilbertSchmidt.IsHilbertSchmidt (F i)) :
    HilbertSchmidt.IsHilbertSchmidt (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa only [Finset.sum_empty] using
        (HilbertSchmidt.isHilbertSchmidt_zero (H := H))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (HilbertSchmidt.isHilbertSchmidt_add (hF i) ih)

/-- A finite sum of products sharing an S₂ left factor is S₁.
The proof first sums the right factors in S₂ and uses the
general two-Hilbert--Schmidt product theorem once. -/
theorem isTraceClass_finset_products_common_left_HS
    {ι : Type*} (s : Finset ι)
    (R : H →L[ℂ] H) (S : ι → H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : ∀ i, HilbertSchmidt.IsHilbertSchmidt (S i)) :
    IsTraceClass (∑ i ∈ s, R * S i) := by
  classical
  have hsum := isHilbertSchmidt_finset_sum s S hS
  have hp : IsTraceClass (R * (∑ i ∈ s, S i)) :=
    isTraceClass_mul_of_twoHilbertSchmidt R (∑ i ∈ s, S i) hR hsum
  have heq : R * (∑ i ∈ s, S i) = ∑ i ∈ s, R * S i := by
    -- These local witnesses depend on s; remove them from this purely
    -- algebraic induction so its inductive hypothesis stays unconditional.
    clear hsum hp
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi, mul_add, ih]
  rw [← heq]
  exact hp

#print axioms ProbabilisticTheory.isTraceClass_add_common_left_HS
#print axioms ProbabilisticTheory.isTraceClass_add_common_right_HS
#print axioms ProbabilisticTheory.isHilbertSchmidt_finset_sum
#print axioms ProbabilisticTheory.isTraceClass_finset_products_common_left_HS

end ProbabilisticTheory
