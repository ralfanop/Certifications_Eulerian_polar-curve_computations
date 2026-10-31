import GegenbauerFock.PhyslibPositiveTraceAddNorm

/-!
# V007 — finite positive S₁ sums and arbitrary Gram conjugations

The general positive-addition theorem is promoted from two summands
to any finite family, with a **common actual Hilbert basis**.
For the concrete ultraspherical Fock operator all conjugated Grams
admit a summable diagonal on every source Hilbert basis.

This module concerns genuine CFC-absolute trace-class membership.
It does NOT assert arbitrary nonpositive trace-class addition,
a general Schatten S₁ normed group, or completeness.

No change to certified sources, V097, pins, or the handover.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A finite sum of positive Hilbert endomorphisms is trace-class
if every summand has a summable real diagonal on one fixed complete
Hilbert basis. No finite-dimensionality or commutativity hypothesis. -/
theorem isTraceClass_finset_sum_of_nonneg_sameBasis
    {ι : Type*} (s : Finset ι) (A : ι → H →L[ℂ] H)
    (hA : ∀ i, 0 ≤ A i)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hdiag : ∀ i, Summable (fun j : w =>
      (inner ℂ (b j) (A i (b j))).re)) :
    IsTraceClass (∑ i ∈ s, A i) := by
  classical
  have hpos : 0 ≤ ∑ i ∈ s, A i :=
    Finset.sum_nonneg (fun i _ => hA i)
  have hs : ∀ t : Finset ι, Summable (fun j : w =>
      (inner ℂ (b j) ((∑ i ∈ t, A i) (b j))).re) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        simpa using (summable_zero : Summable (fun _ : w => (0 : ℝ)))
    | @insert i t hit ih =>
        have hadd := (hdiag i).add ih
        simpa only [Finset.sum_insert hit, ContinuousLinearMap.add_apply,
          inner_add_right, Complex.add_re] using hadd
  exact isTraceClass_of_nonneg_of_summable
    (∑ i ∈ s, A i) hpos b (hs s)

#print axioms ProbabilisticTheory.isTraceClass_finset_sum_of_nonneg_sameBasis

end ProbabilisticTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- A true finite sum of (potentially infinite-rank) positive Gram
conjugations indexed by arbitrary finitely many bounded source maps. -/
noncomputable def gramFiniteSum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  ∑ i ∈ s, gramAfterRight lam alpha hlam ha (B i)

/-- Every finite Gram family is positive, without any condition
on mutual commutators of its bounded preconditioners. -/
theorem gramFiniteSum_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    0 ≤ gramFiniteSum lam alpha hlam ha s B := by
  unfold gramFiniteSum
  exact Finset.sum_nonneg (fun i _ =>
    gramAfterRight_nonneg lam alpha hlam ha (B i))

private theorem finite_re_inner_swap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

private theorem gramAfterRight_finBasis_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
    {w : Set (Lp ℂ 2 (Ultraspherical.measure lam))}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun j : w =>
      (inner ℂ (b j)
        (gramAfterRight lam alpha hlam ha B (b j))).re) := by
  have hHS : Summable (fun j : w =>
      ‖((C lam alpha hlam ha).comp B) (b j)‖ ^ 2) :=
    C_comp_right_isHilbertSchmidt lam alpha hlam ha B b
  apply hHS.congr
  intro j
  exact (HilbertGram.gram_norm_sq
    ((C lam alpha hlam ha).comp B) (b j)).trans
    (finite_re_inner_swap
      (gramAfterRight lam alpha hlam ha B (b j)) (b j))

/-- Unconditional **CFC trace-class membership** of every finite sum
of conjugated ultraspherical Grams, with arbitrary bounded preconditioners. -/
theorem gramFiniteSum_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.IsTraceClass
      (gramFiniteSum lam alpha hlam ha s B) := by
  unfold gramFiniteSum
  obtain ⟨w, b, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (Ultraspherical.measure lam))
  exact ProbabilisticTheory.isTraceClass_finset_sum_of_nonneg_sameBasis
    s (fun i => gramAfterRight lam alpha hlam ha (B i))
    (fun i => gramAfterRight_nonneg lam alpha hlam ha (B i))
    b (fun i => gramAfterRight_finBasis_summable lam alpha hlam ha (B i) b)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramFiniteSum_nonneg
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramFiniteSum_isTraceClass

end GegenbauerFock.GeneralUltrasphericalFock
