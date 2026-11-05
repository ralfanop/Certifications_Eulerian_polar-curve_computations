import GegenbauerFock.PhyslibPositiveTraceAdd

/-!
# V007 — genuinely general positive trace-class finite-family closure

This theorem is independent of the Eulerian/Gegenbauer model. It shows
that arbitrary finite sums of positive bounded operators on ANY
complete complex Hilbert space are trace class whenever their real
diagonals are summable on ONE common complete Hilbert basis.

No finite-dimensionality hypothesis, change to Lean/Mathlib, or
assumed trace-class additivity for arbitrary nonpositive operators.

This generalizes PhyslibPositiveTraceAdd's certified two-term result.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem positiveFiniteFamily_diagonal
    {ι : Type*} (s : Finset ι)
    (A : ι → H →L[ℂ] H)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (j : w) :
    (inner ℂ (b j) ((∑ i ∈ s, A i) (b j))).re =
      ∑ i ∈ s, (inner ℂ (b j) (A i (b j))).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi,
        ContinuousLinearMap.add_apply,
        inner_add_right, Complex.add_re, ih]

private theorem positiveFiniteFamily_summable
    {ι : Type*} (s : Finset ι)
    (A : ι → H →L[ℂ] H)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hs : ∀ i, Summable (fun j : w =>
      (inner ℂ (b j) (A i (b j))).re)) :
    Summable (fun j : w =>
      (inner ℂ (b j) ((∑ i ∈ s, A i) (b j))).re) := by
  classical
  simp only [positiveFiniteFamily_diagonal s A b]
  induction s using Finset.induction_on with
  | empty =>
      simpa using (summable_zero : Summable (fun _ : w => (0 : ℝ)))
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using (hs i).add ih

/-- Generic finite positive cone closure of source-compatible Physlib
infinite-dimensional CFC trace-class membership. No restriction on
finite rank, dimension, model, or pairwise commutativity. -/
theorem isTraceClass_finset_sum_of_nonneg_sameBasis
    {ι : Type*} (s : Finset ι)
    (A : ι → H →L[ℂ] H)
    (hA : ∀ i, 0 ≤ A i)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hs : ∀ i, Summable (fun j : w =>
      (inner ℂ (b j) (A i (b j))).re)) :
    IsTraceClass (∑ i ∈ s, A i) := by
  classical
  have hpos : 0 ≤ ∑ i ∈ s, A i :=
    Finset.sum_nonneg (fun i _ => hA i)
  exact isTraceClass_of_nonneg_of_summable
    (∑ i ∈ s, A i) hpos b
    (positiveFiniteFamily_summable s A b hs)

#print axioms ProbabilisticTheory.isTraceClass_finset_sum_of_nonneg_sameBasis

end ProbabilisticTheory
