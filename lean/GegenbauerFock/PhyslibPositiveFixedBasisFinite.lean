import GegenbauerFock.PhyslibPositiveFixedBasis

/-!
# V007 — finite positive sums on one Hilbert basis

For a fixed complete Hilbert basis of an arbitrary complex Hilbert space,
finite sums of positive operators with summable diagonals remain in the same
cone, and their fixed-basis diagonal trace is exactly additive.

The result concerns a fixed Hilbert basis. It is not a claim of
basis-independence of arbitrary trace-class witnesses, general S1 additivity,
a triangle inequality, or Banach completeness.
-/

noncomputable section

namespace ProbabilisticTheory.PositiveFixedBasis

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {w : Set H} (b : HilbertBasis w ℂ H)

/-- An arbitrary finite positive sum, with actual diagonal summability
on the same complete Hilbert basis. -/
def finiteSum {ι : Type*} (s : Finset ι)
    (X : ι → ProbabilisticTheory.PositiveFixedBasis w b) :
    ProbabilisticTheory.PositiveFixedBasis w b where
  op := ∑ i ∈ s, (X i).op
  op_nonneg := Finset.sum_nonneg (fun i _ => (X i).op_nonneg)
  diagonal_summable := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa using (summable_zero : Summable (fun _ : w => (0 : ℝ)))
    | @insert i s hi ih =>
        simpa only [Finset.sum_insert hi,
          ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
          using (X i).diagonal_summable.add ih

/-- The underlying operator is literally the finite sum of the inputs. -/
@[simp] theorem finiteSum_op {ι : Type*} (s : Finset ι)
    (X : ι → ProbabilisticTheory.PositiveFixedBasis w b) :
    (finiteSum b s X).op = ∑ i ∈ s, (X i).op := rfl

/-- Additivity of the genuine fixed-basis diagonal series
under arbitrary finite positive sums, with no finite-rank restriction. -/
theorem diagonalTrace_finiteSum {ι : Type*} (s : Finset ι)
    (X : ι → ProbabilisticTheory.PositiveFixedBasis w b) :
    diagonalTrace b (finiteSum b s X) =
      ∑ i ∈ s, diagonalTrace b (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteSum, diagonalTrace]
  | @insert i s hi ih =>
      change
        (∑' j : w,
          (inner ℂ (b j)
            ((∑ k ∈ insert i s, (X k).op) (b j))).re) =
        ∑ k ∈ insert i s, diagonalTrace b (X k)
      simp only [Finset.sum_insert hi,
        ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
      have hs : Summable (fun j : w =>
          (inner ℂ (b j)
            ((∑ k ∈ s, (X k).op) (b j))).re) :=
        (finiteSum b s X).diagonal_summable
      rw [(X i).diagonal_summable.tsum_add hs]
      change diagonalTrace b (X i) + diagonalTrace b (finiteSum b s X) =
        diagonalTrace b (X i) + ∑ k ∈ s, diagonalTrace b (X k)
      exact congrArg (fun t => diagonalTrace b (X i) + t) ih

/-- The actual sum belongs to the source-compatible Physlib CFC class. -/
theorem finiteSum_isTraceClass {ι : Type*} (s : Finset ι)
    (X : ι → ProbabilisticTheory.PositiveFixedBasis w b) :
    ProbabilisticTheory.IsTraceClass (∑ i ∈ s, (X i).op) := by
  simpa only [← finiteSum_op b s X] using
    (isTraceClass b (finiteSum b s X))

#print axioms ProbabilisticTheory.PositiveFixedBasis.finiteSum_op
#print axioms ProbabilisticTheory.PositiveFixedBasis.diagonalTrace_finiteSum
#print axioms ProbabilisticTheory.PositiveFixedBasis.finiteSum_isTraceClass

end ProbabilisticTheory.PositiveFixedBasis
