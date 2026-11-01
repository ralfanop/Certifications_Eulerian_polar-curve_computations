import GegenbauerFock.PhyslibFinitePositiveTrace

/-!
# V007 — finite positive Gram sums: exact trace norm and Kummer bound

The preceding module proves source-compatible CFC S₁ membership for
finite families of genuinely bounded Gram conjugations. Here we
identify the **actual** CFC trace norm with the sum of individual
trace norms and their certified row energies, without invoking a
yet-unproved general trace-norm triangle inequality.

All basis changes are justified by the previously checked concrete
Gram row-energy identity. No new assumptions, sorry or axioms.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

private theorem finiteFamily_re_inner_swap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

private theorem finiteFamily_diagonal_summable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
    {w : Set (Lp ℂ 2 (Ultraspherical.measure lam))}
    (b : HilbertBasis w ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    Summable (fun j : w =>
      (inner ℂ (b j) (gramAfterRight lam alpha hlam ha B (b j))).re) := by
  have hHS : Summable (fun j : w =>
      ‖((C lam alpha hlam ha).comp B) (b j)‖ ^ 2) :=
    C_comp_right_isHilbertSchmidt lam alpha hlam ha B b
  apply hHS.congr
  intro j
  exact (HilbertGram.gram_norm_sq ((C lam alpha hlam ha).comp B) (b j)).trans
    (finiteFamily_re_inner_swap
      (gramAfterRight lam alpha hlam ha B (b j)) (b j))

/-- Finite interchange of a genuine summable infinite real series
and an arbitrary finite sum, without any topological shortcuts. -/
private theorem tsum_finset_sum
    {ι κ : Type*} (s : Finset ι) (f : ι → κ → ℝ)
    (hf : ∀ i, Summable (f i)) :
    (∑' j : κ, ∑ i ∈ s, f i j) =
      ∑ i ∈ s, ∑' j : κ, f i j := by
  classical
  have hsum (t : Finset ι) :
      Summable (fun j : κ => ∑ i ∈ t, f i j) := by
    induction t using Finset.induction_on with
    | empty =>
        simpa using (summable_zero : Summable (fun _ : κ => (0 : ℝ)))
    | @insert i t hit ih =>
        simpa only [Finset.sum_insert hit] using (hf i).add ih
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hit ih =>
      calc
        (∑' j : κ, ∑ k ∈ insert i s, f k j) =
          ∑' j : κ, (f i j + ∑ k ∈ s, f k j) := by
            simp only [Finset.sum_insert hit]
        _ = (∑' j : κ, f i j) +
              (∑' j : κ, ∑ k ∈ s, f k j) :=
          (hf i).tsum_add (hsum s)
        _ = ∑ k ∈ insert i s, ∑' j : κ, f k j := by
          rw [ih, Finset.sum_insert hit]

private theorem diagonal_finset_operator_sum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Type*} (s : Finset ι) (A : ι → H →L[ℂ] H)
    (x : H) :
    (inner ℂ x ((∑ i ∈ s, A i) x)).re =
      ∑ i ∈ s, (inner ℂ x (A i x)).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hit ih =>
      simp only [Finset.sum_insert hit, ContinuousLinearMap.add_apply,
        inner_add_right, Complex.add_re, ih]

/-- CFC trace norm of a finite sum of positive ultraspherical Grams
equals the sum of each genuine trace norm, for arbitrary bounded
source preconditioners; their pairwise commutators are unrestricted. -/
theorem gramFiniteSum_traceNorm_eq_sum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
      (gramFiniteSum lam alpha hlam ha s B)
      (gramFiniteSum_isTraceClass lam alpha hlam ha s B) =
    ∑ i ∈ s,
      ProbabilisticTheory.traceNorm
        (gramAfterRight lam alpha hlam ha (B i))
        (gramAfterRight_isTraceClass lam alpha hlam ha (B i)) := by
  classical
  let h := gramFiniteSum_isTraceClass lam alpha hlam ha s B
  let b := h.choose_spec.choose
  have hdiag : ∀ i : ι, Summable (fun j : h.choose =>
      (inner ℂ (b j) (gramAfterRight lam alpha hlam ha (B i) (b j))).re) :=
    fun i => finiteFamily_diagonal_summable lam alpha hlam ha (B i) b
  change ProbabilisticTheory.traceNorm (gramFiniteSum lam alpha hlam ha s B) h = _
  rw [ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg
    (gramFiniteSum lam alpha hlam ha s B)
    (gramFiniteSum_nonneg lam alpha hlam ha s B) h]
  calc
    (∑' j : h.choose,
      (inner ℂ (b j)
        (gramFiniteSum lam alpha hlam ha s B (b j))).re) =
      ∑' j : h.choose,
        ∑ i ∈ s,
          (inner ℂ (b j)
            (gramAfterRight lam alpha hlam ha (B i) (b j))).re := by
              apply tsum_congr
              intro j
              simpa only [gramFiniteSum] using
                (diagonal_finset_operator_sum s
                  (fun i => gramAfterRight lam alpha hlam ha (B i)) (b j))
    _ = ∑ i ∈ s,
          ∑' j : h.choose,
            (inner ℂ (b j)
              (gramAfterRight lam alpha hlam ha (B i) (b j))).re :=
      tsum_finset_sum s
        (fun i j =>
          (inner ℂ (b j)
            (gramAfterRight lam alpha hlam ha (B i) (b j))).re)
        hdiag
    _ = ∑ i ∈ s,
          ProbabilisticTheory.traceNorm
            (gramAfterRight lam alpha hlam ha (B i))
            (gramAfterRight_isTraceClass lam alpha hlam ha (B i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [gramAfterRight_basisTrace_eq_rowMass
        lam alpha hlam ha (B i) b,
        gramAfterRight_traceNorm_eq_composedRowMass lam alpha hlam ha (B i)]

/-- Exact finite-family Schatten-S₁ bound from positive Gram
additivity and the independent source-side S₂ quadratic estimates. -/
theorem gramFiniteSum_traceNorm_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι)
    (B : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
      (gramFiniteSum lam alpha hlam ha s B)
      (gramFiniteSum_isTraceClass lam alpha hlam ha s B) ≤
    (∑ i ∈ s, ‖B i‖ ^ 2) *
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [gramFiniteSum_traceNorm_eq_sum]
  calc
    (∑ i ∈ s, ProbabilisticTheory.traceNorm
        (gramAfterRight lam alpha hlam ha (B i))
        (gramAfterRight_isTraceClass lam alpha hlam ha (B i))) ≤
      ∑ i ∈ s, ‖B i‖ ^ 2 *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
          apply Finset.sum_le_sum
          intro i _
          exact gramAfterRight_traceNorm_le_kummer lam alpha hlam ha (B i)
    _ = (∑ i ∈ s, ‖B i‖ ^ 2) *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
          rw [Finset.sum_mul]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramFiniteSum_traceNorm_eq_sum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramFiniteSum_traceNorm_le_kummer

end GegenbauerFock.GeneralUltrasphericalFock
