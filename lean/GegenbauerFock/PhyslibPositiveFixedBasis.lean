import GegenbauerFock.PhyslibTraceClassScalar

/-!
# V007 — positive trace-class cone relative to a fixed Hilbert basis

An incremental, noncircular step toward the general trace-class Banach
space.  For an arbitrary complete complex Hilbert space and a *fixed*
complete Hilbert basis, the positive operators whose diagonal is summable
form an additive cone.  Its explicitly basis-dependent diagonal trace
is nonnegative and additive.  Every such operator is genuinely trace
class in the source-compatible CFC-absolute Physlib predicate.

Importantly, the diagonal trace here is NOT silently identified with
the witness-selected traceNorm for an arbitrary different basis.
Basis-independence, unrestricted non-self-adjoint S₁ addition,
triangle inequality, and completion remain separate obligations.
The original V007/Physlib source files are unchanged.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Positive bounded endomorphisms with summable diagonal on a specified
complete Hilbert basis, retaining both witnesses as data. -/
structure PositiveFixedBasis (w : Set H) (b : HilbertBasis w ℂ H) where
  op : H →L[ℂ] H
  op_nonneg : 0 ≤ op
  diagonal_summable :
    Summable (fun i : w => (inner ℂ (b i) (op (b i))).re)

namespace PositiveFixedBasis

variable {w : Set H} (b : HilbertBasis w ℂ H)

/-- The zero endomorphism belongs to the fixed-basis positive cone. -/
def zero : PositiveFixedBasis w b where
  op := 0
  op_nonneg := le_refl 0
  diagonal_summable := by
    simpa using (summable_zero : Summable (fun _ : w => (0 : ℝ)))

/-- Closure under addition of arbitrary positive summable-diagonal maps.
There is no finite-rank, commutativity or dimension hypothesis. -/
def add (X Y : PositiveFixedBasis w b) : PositiveFixedBasis w b where
  op := X.op + Y.op
  op_nonneg := add_nonneg X.op_nonneg Y.op_nonneg
  diagonal_summable := by
    simpa only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
      using X.diagonal_summable.add Y.diagonal_summable

/-- A fixed-basis diagonal trace, as opposed to the globally
basis-independent trace, which requires an additional theorem. -/
def diagonalTrace (X : PositiveFixedBasis w b) : ℝ :=
  ∑' i : w, (inner ℂ (b i) (X.op (b i))).re

/-- Every element of the positive fixed-basis cone belongs to the
actual CFC-absolute Physlib-compatible trace class. -/
theorem isTraceClass (X : PositiveFixedBasis w b) : IsTraceClass X.op :=
  isTraceClass_of_nonneg_of_summable
    X.op X.op_nonneg b X.diagonal_summable

/-- Additivity of the fixed-basis diagonal trace for all positive
summable-diagonal endomorphisms. -/
theorem diagonalTrace_add (X Y : PositiveFixedBasis w b) :
    diagonalTrace b (add b X Y) =
      diagonalTrace b X + diagonalTrace b Y := by
  unfold diagonalTrace
  change (∑' i : w,
      (inner ℂ (b i) ((X.op + Y.op) (b i))).re) = _
  simpa only [ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    using X.diagonal_summable.tsum_add Y.diagonal_summable

/-- The fixed-basis trace is nonnegative. -/
theorem diagonalTrace_nonneg (X : PositiveFixedBasis w b) :
    0 ≤ diagonalTrace b X := by
  unfold diagonalTrace
  apply tsum_nonneg
  intro i
  exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp X.op_nonneg).re_inner_nonneg_right (b i)

/-- An arbitrary Physlib-compatible trace-class operator provides,
through its CFC absolute value, an element of a fixed-basis positive
cone.  The basis here is precisely the one carried by its witness. -/
def absolute (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    PositiveFixedBasis hT.choose hT.choose_spec.choose where
  op := CFC.abs T
  op_nonneg := CFC.abs_nonneg T
  diagonal_summable := hT.choose_spec.choose_spec

/-- The witness-selected CFC trace norm is exactly the diagonal trace
of its positive absolute value on that very same witness basis. -/
theorem diagonalTrace_absolute (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    diagonalTrace hT.choose_spec.choose (absolute T hT) =
      traceNorm T hT := rfl

#print axioms ProbabilisticTheory.PositiveFixedBasis.isTraceClass
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_add
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_nonneg
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_absolute

end PositiveFixedBasis
end ProbabilisticTheory
