import GegenbauerFock.PhyslibPositiveFixedBasis

/-!
# V007 — positive fixed-basis trace cone as an additive commutative monoid

This module upgrades the already kernel-checked `PositiveFixedBasis`
construction to an actual additive commutative monoid.  Its genuine
summable fixed-basis diagonal trace is an additive monoid homomorphism.
Every resulting finite sum remains in the CFC-based Physlib-compatible S1
predicate.  None of these assertions is a general addition or trace-norm
triangle theorem for arbitrary nonpositive trace-class operators.

All statements are valid in arbitrary complete complex Hilbert spaces;
no commutativity or finite-rank assumption is imposed on the positive
summands.  The diagonal trace remains explicitly *basis dependent* until
a separate basis-independence theorem has been certified.
-/

noncomputable section

namespace ProbabilisticTheory.PositiveFixedBasis

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {w : Set H} (b : HilbertBasis w ℂ H)

/-- Two positive fixed-basis elements are equal if their actual
bounded operators are equal. The positivity and summability witnesses
are proof-irrelevant. -/
private theorem ext_op {X Y : PositiveFixedBasis w b}
    (h : X.op = Y.op) : X = Y := by
  cases X with
  | mk op hx hs =>
    cases Y with
    | mk op' hy ht =>
      cases h
      rfl

/-- The full fixed-basis positive cone (not the whole S1 space)
is an additive commutative monoid. -/
noncomputable instance : AddCommMonoid (PositiveFixedBasis w b) where
  zero := PositiveFixedBasis.zero b
  add := PositiveFixedBasis.add b
  add_assoc X Y Z := by
    apply ext_op b
    change (X.op + Y.op) + Z.op = X.op + (Y.op + Z.op)
    exact add_assoc _ _ _
  zero_add X := by
    apply ext_op b
    change (0 : H →L[ℂ] H) + X.op = X.op
    exact zero_add _
  add_zero X := by
    apply ext_op b
    change X.op + (0 : H →L[ℂ] H) = X.op
    exact add_zero _
  add_comm X Y := by
    apply ext_op b
    change X.op + Y.op = Y.op + X.op
    exact add_comm _ _
  nsmul := nsmulRec

@[simp] theorem op_zero :
    (0 : PositiveFixedBasis w b).op = (0 : H →L[ℂ] H) := rfl

@[simp] theorem op_add (X Y : PositiveFixedBasis w b) :
    (X + Y).op = X.op + Y.op := rfl

/-- Zero has zero fixed-basis diagonal trace. -/
@[simp] theorem diagonalTrace_zero :
    diagonalTrace b (0 : PositiveFixedBasis w b) = 0 := by
  change (∑' i : w, (inner ℂ (b i)
    ((0 : H →L[ℂ] H) (b i))).re) = 0
  simp

/-- Additivity for the genuine positive cone trace, stated using
the additive-monoid operations rather than the old constructor. -/
theorem diagonalTrace_add_monoid (X Y : PositiveFixedBasis w b) :
    diagonalTrace b (X + Y) =
      diagonalTrace b X + diagonalTrace b Y :=
  diagonalTrace_add b X Y

/-- An actual additive monoid homomorphism from the positive cone
to the additive real numbers. -/
noncomputable def diagonalTraceHom : PositiveFixedBasis w b →+ ℝ where
  toFun := diagonalTrace b
  map_zero' := diagonalTrace_zero b
  map_add' := diagonalTrace_add_monoid b

/-- Every finite sum in the positive cone remains in genuine
Physlib-compatible S1, with no finite-rank requirement. -/
theorem finset_sum_isTraceClass {ι : Type*}
    (s : Finset ι) (X : ι → PositiveFixedBasis w b) :
    ProbabilisticTheory.IsTraceClass ((∑ i ∈ s, X i).op) :=
  isTraceClass b (∑ i ∈ s, X i)

/-- Exact additivity of the fixed-basis positive trace on finite sums. -/
theorem diagonalTrace_finset_sum {ι : Type*}
    (s : Finset ι) (X : ι → PositiveFixedBasis w b) :
    diagonalTrace b (∑ i ∈ s, X i) =
      ∑ i ∈ s, diagonalTrace b (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, diagonalTrace_zero b]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, diagonalTrace_add_monoid b,
        ih, Finset.sum_insert hi]

#print axioms ProbabilisticTheory.PositiveFixedBasis.op_add
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_zero
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_add_monoid
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTraceHom
#print axioms ProbabilisticTheory.PositiveFixedBasis.finset_sum_isTraceClass
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_finset_sum

end ProbabilisticTheory.PositiveFixedBasis
