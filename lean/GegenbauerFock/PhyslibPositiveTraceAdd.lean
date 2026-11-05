import GegenbauerFock.PhyslibGramConjugationIdeal

/-!
# V007 — additive closure for jointly diagonally summable positive S₁ maps

The pinned Mathlib / source-compatible Physlib CFC definition of S₁
allows a rigorous *shared-Hilbert-basis* positive-addition theorem.
Applied to V007, this proves actual trace-class membership for
sums of two arbitrary bounded conjugations of the ultraspherical
Gram operator, not just finite-rank surrogates.

This does NOT assert full additive closure for general (possibly
nonpositive) trace-class maps or a normed Banach S₁ subtype.
The approved V007 handover and all previous certified files stay intact.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Sum of two positive Hilbert operators is genuinely trace-class
when their (real) diagonals are summable on the SAME complete basis.
There is no finite-dimensionality assumption and no unproved
basis-independence step hidden in this statement. -/
theorem isTraceClass_add_of_nonneg_sameBasis
    (A B : H →L[ℂ] H) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hAs : Summable (fun i : w =>
      (inner ℂ (b i) (A (b i))).re))
    (hBs : Summable (fun i : w =>
      (inner ℂ (b i) (B (b i))).re)) :
    IsTraceClass (A + B) := by
  refine ⟨w, b, ?_⟩
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  simpa only [CFC.abs_of_nonneg (A + B) hAB,
    ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    using hAs.add hBs

#print axioms ProbabilisticTheory.isTraceClass_add_of_nonneg_sameBasis

end ProbabilisticTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Positive sum of two arbitrary bounded source-conjugated
ultraspherical Gram operators, as an actual L² bounded endomorphism. -/
noncomputable def gramAfterRightPair
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  gramAfterRight lam alpha hlam ha B +
    gramAfterRight lam alpha hlam ha D

theorem gramAfterRightPair_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    0 ≤ gramAfterRightPair lam alpha hlam ha B D := by
  exact add_nonneg
    (gramAfterRight_nonneg lam alpha hlam ha B)
    (gramAfterRight_nonneg lam alpha hlam ha D)

/-- Conjugate-first Mathlib inner-product convention: equality
of real diagonal values after swapping the two entries. -/
private theorem pair_re_inner_swap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- Diagonal summability holds on EVERY complete source Hilbert basis,
from the certified two-sided S₂ theory, not only on an existential
trace-class witness basis. -/
private theorem gramAfterRight_basisDiagonal_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
    {w : Set (Lp ℂ 2 (Ultraspherical.measure lam))}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun i : w =>
      (inner ℂ (b i)
        (gramAfterRight lam alpha hlam ha B (b i))).re) := by
  have hs : Summable (fun i : w =>
      ‖((C lam alpha hlam ha).comp B) (b i)‖ ^ 2) :=
    C_comp_right_isHilbertSchmidt lam alpha hlam ha B b
  apply hs.congr
  intro i
  have hnorm :=
    HilbertGram.gram_norm_sq ((C lam alpha hlam ha).comp B) (b i)
  exact hnorm.trans
    (pair_re_inner_swap
      (gramAfterRight lam alpha hlam ha B (b i)) (b i))

/-- The sum of two nontrivial, generally infinite-rank conjugated
Gegenbauer–Fock Gram maps belongs to the genuine CFC-based S₁ class.
The arbitrary bounded preconditioners B and D need not commute. -/
theorem gramAfterRightPair_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.IsTraceClass
      (gramAfterRightPair lam alpha hlam ha B D) := by
  change ProbabilisticTheory.IsTraceClass
    (gramAfterRight lam alpha hlam ha B +
      gramAfterRight lam alpha hlam ha D)
  obtain ⟨w, b, _⟩ :=
    exists_hilbertBasis ℂ (Lp ℂ 2 (Ultraspherical.measure lam))
  exact ProbabilisticTheory.isTraceClass_add_of_nonneg_sameBasis
    (gramAfterRight lam alpha hlam ha B)
    (gramAfterRight lam alpha hlam ha D)
    (gramAfterRight_nonneg lam alpha hlam ha B)
    (gramAfterRight_nonneg lam alpha hlam ha D)
    b
    (gramAfterRight_basisDiagonal_summable lam alpha hlam ha B b)
    (gramAfterRight_basisDiagonal_summable lam alpha hlam ha D b)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRightPair_nonneg
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRightPair_isTraceClass

end GegenbauerFock.GeneralUltrasphericalFock
