import GegenbauerFock.PhyslibPositiveFixedBasis

/-!
# V007 — additive commutative monoid of fixed-basis positive S₁ operators

For an arbitrary complex complete Hilbert space H and one fixed
Hilbert basis b, the cone of positive endomorphisms with summable
b-diagonals is an additive commutative monoid. The diagonal trace
is additive and nonnegative. All its operators satisfy the genuine
CFC-absolute Physlib-compatible S₁ membership predicate.

This is an actual infinite-dimensional positive cone; it is NOT
the entire non-selfadjoint trace class and does not construct its
Banach trace norm. No unproved basis-invariance assumption is used.
-/

noncomputable section

namespace ProbabilisticTheory.PositiveFixedBasis

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {w : Set H} (b : HilbertBasis w ℂ H)

/-- Positive fixed-basis S₁ elements are determined by the actual
bounded operator: all membership certificates are propositions. -/
@[ext] theorem ext {X Y : PositiveFixedBasis w b}
    (h : X.op = Y.op) : X = Y := by
  cases X with
  | mk x hx hs =>
    cases Y with
    | mk y hy ht =>
      cases h
      rfl

/-- The positive cone is a commutative additive monoid in
arbitrary Hilbert dimension (no finite-rank restriction). -/
noncomputable instance : AddCommMonoid (PositiveFixedBasis w b) where
  zero := PositiveFixedBasis.zero b
  add := PositiveFixedBasis.add b
  nsmul := nsmulRec
  zero_add X := by
    apply ext b
    change (0 : H →L[ℂ] H) + X.op = X.op
    exact zero_add X.op
  add_zero X := by
    apply ext b
    change X.op + (0 : H →L[ℂ] H) = X.op
    exact add_zero X.op
  add_assoc X Y Z := by
    apply ext b
    change (X.op + Y.op) + Z.op = X.op + (Y.op + Z.op)
    exact add_assoc X.op Y.op Z.op
  add_comm X Y := by
    apply ext b
    change X.op + Y.op = Y.op + X.op
    exact add_comm X.op Y.op

/-- The concrete forgetful map respects the new monoid structure. -/
@[simp] theorem op_add (X Y : PositiveFixedBasis w b) :
    (X + Y).op = X.op + Y.op := rfl

@[simp] theorem op_zero :
    (0 : PositiveFixedBasis w b).op = (0 : H →L[ℂ] H) := rfl

/-- The positive diagonal trace is a genuine additive functional
on the fixed-basis positive S₁ monoid. -/
theorem diagonalTrace_add_monoid (X Y : PositiveFixedBasis w b) :
    diagonalTrace b (X + Y) =
      diagonalTrace b X + diagonalTrace b Y :=
  diagonalTrace_add b X Y

/-- The zero cone element has zero diagonal trace. -/
@[simp] theorem diagonalTrace_zero_monoid :
    diagonalTrace b (0 : PositiveFixedBasis w b) = 0 := by
  unfold diagonalTrace
  simp [op_zero]

/-- Every element of the additive positive cone is genuinely
trace class under the imported functional-calculus absolute value. -/
theorem sum_isTraceClass (X Y : PositiveFixedBasis w b) :
    IsTraceClass (X + Y).op :=
  isTraceClass b (X + Y)

#print axioms ProbabilisticTheory.PositiveFixedBasis.ext
#print axioms ProbabilisticTheory.PositiveFixedBasis.op_add
#print axioms ProbabilisticTheory.PositiveFixedBasis.op_zero
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_add_monoid
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_zero_monoid
#print axioms ProbabilisticTheory.PositiveFixedBasis.sum_isTraceClass

end ProbabilisticTheory.PositiveFixedBasis
