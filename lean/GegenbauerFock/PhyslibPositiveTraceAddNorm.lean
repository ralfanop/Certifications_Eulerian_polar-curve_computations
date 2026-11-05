import GegenbauerFock.PhyslibPositiveTraceAdd

/-!
# V007 — exact positive S₁ trace-norm additivity for two conjugated Grams

An independent post-checkpoint module, avoiding any alteration of
earlier certified sources. For arbitrary bounded source maps B and D,
the genuine CFC trace norm of the positive operator
  (C ∘ B)† (C ∘ B) + (C ∘ D)† (C ∘ D)
is exactly the sum of its two CFC trace norms, and is bounded by
(||B||² + ||D||²) times the exact ultraspherical Kummer energy.

Only positive-operator additivity is claimed. General S₁ addition,
the norm triangle inequality and Banach completeness remain separate.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

private theorem pairTrace_re_inner_swap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x y : E) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- The diagonal trace of any preconditioned Gegenbauer--Fock Gram
on ANY complete source Hilbert basis is its genuine squared row energy. -/
theorem gramAfterRight_basisTrace_eq_rowMass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
    {ι : Type*}
    (b : HilbertBasis ι ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) :
    (∑' i : ι,
      (inner ℂ (b i)
        (gramAfterRight lam alpha hlam ha B (b i))).re) =
    ∑' n : ℕ,
      ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2 := by
  calc
    (∑' i : ι,
      (inner ℂ (b i)
        (gramAfterRight lam alpha hlam ha B (b i))).re) =
      ∑' i : ι, ‖((C lam alpha hlam ha).comp B) (b i)‖ ^ 2 := by
        apply tsum_congr
        intro i
        exact (pairTrace_re_inner_swap
          (b i) (gramAfterRight lam alpha hlam ha B (b i))).trans
          (HilbertGram.gram_norm_sq
            ((C lam alpha hlam ha).comp B) (b i)).symm
    _ = ∑' n : ℕ,
        ‖SummableRowsCompact.row ((C lam alpha hlam ha).comp B) n‖ ^ 2 :=
      (FockEnergy.summableRows_iff_sourceBasis_energy
        ((C lam alpha hlam ha).comp B)
        (C_comp_right_rows_summable lam alpha hlam ha B) b).2
    _ = ∑' n : ℕ,
        ‖(SummableRowsCompact.row (C lam alpha hlam ha) n).comp B‖ ^ 2 := by
          apply tsum_congr
          intro n
          rw [C_row_comp_right lam alpha hlam ha B n]

private theorem gramAfterRight_pairBasis_summable
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
  have hn :=
    HilbertGram.gram_norm_sq ((C lam alpha hlam ha).comp B) (b i)
  exact hn.trans
    (pairTrace_re_inner_swap
      (gramAfterRight lam alpha hlam ha B (b i)) (b i))

/-- Exact CFC absolute trace-norm additivity for two positive
conjugations of the actual infinite-dimensional ultraspherical Gram.
Neither B nor D need commute with the other or the Gram. -/
theorem gramAfterRightPair_traceNorm_add
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
      (gramAfterRightPair lam alpha hlam ha B D)
      (gramAfterRightPair_isTraceClass lam alpha hlam ha B D) =
    ProbabilisticTheory.traceNorm
      (gramAfterRight lam alpha hlam ha B)
      (gramAfterRight_isTraceClass lam alpha hlam ha B) +
    ProbabilisticTheory.traceNorm
      (gramAfterRight lam alpha hlam ha D)
      (gramAfterRight_isTraceClass lam alpha hlam ha D) := by
  let h := gramAfterRightPair_isTraceClass lam alpha hlam ha B D
  have hB := gramAfterRight_pairBasis_summable
    lam alpha hlam ha B h.choose_spec.choose
  have hD := gramAfterRight_pairBasis_summable
    lam alpha hlam ha D h.choose_spec.choose
  change ProbabilisticTheory.traceNorm
    (gramAfterRightPair lam alpha hlam ha B D) h = _
  rw [ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg
    (gramAfterRightPair lam alpha hlam ha B D)
    (gramAfterRightPair_nonneg lam alpha hlam ha B D) h]
  calc
    (∑' i : h.choose,
      (inner ℂ (h.choose_spec.choose i)
        (gramAfterRightPair lam alpha hlam ha B D
          (h.choose_spec.choose i))).re) =
      ∑' i : h.choose,
        ((inner ℂ (h.choose_spec.choose i)
          (gramAfterRight lam alpha hlam ha B (h.choose_spec.choose i))).re +
         (inner ℂ (h.choose_spec.choose i)
          (gramAfterRight lam alpha hlam ha D (h.choose_spec.choose i))).re) := by
            apply tsum_congr
            intro i
            simp only [gramAfterRightPair,
              ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]
    _ = (∑' i : h.choose,
          (inner ℂ (h.choose_spec.choose i)
            (gramAfterRight lam alpha hlam ha B (h.choose_spec.choose i))).re) +
        (∑' i : h.choose,
          (inner ℂ (h.choose_spec.choose i)
            (gramAfterRight lam alpha hlam ha D (h.choose_spec.choose i))).re) :=
          hB.tsum_add hD
    _ = ProbabilisticTheory.traceNorm
          (gramAfterRight lam alpha hlam ha B)
          (gramAfterRight_isTraceClass lam alpha hlam ha B) +
        ProbabilisticTheory.traceNorm
          (gramAfterRight lam alpha hlam ha D)
          (gramAfterRight_isTraceClass lam alpha hlam ha D) := by
            rw [gramAfterRight_basisTrace_eq_rowMass
                  lam alpha hlam ha B h.choose_spec.choose,
                gramAfterRight_basisTrace_eq_rowMass
                  lam alpha hlam ha D h.choose_spec.choose,
                gramAfterRight_traceNorm_eq_composedRowMass
                  lam alpha hlam ha B,
                gramAfterRight_traceNorm_eq_composedRowMass
                  lam alpha hlam ha D]

/-- A quantitative positive S₁ ideal estimate in the genuine
CFC-absolute trace norm, sharp for identity preconditioners. -/
theorem gramAfterRightPair_traceNorm_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.traceNorm
      (gramAfterRightPair lam alpha hlam ha B D)
      (gramAfterRightPair_isTraceClass lam alpha hlam ha B D) ≤
    (‖B‖ ^ 2 + ‖D‖ ^ 2) *
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  rw [gramAfterRightPair_traceNorm_add]
  calc
    ProbabilisticTheory.traceNorm
        (gramAfterRight lam alpha hlam ha B)
        (gramAfterRight_isTraceClass lam alpha hlam ha B) +
      ProbabilisticTheory.traceNorm
        (gramAfterRight lam alpha hlam ha D)
        (gramAfterRight_isTraceClass lam alpha hlam ha D) ≤
      ‖B‖ ^ 2 * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) +
      ‖D‖ ^ 2 * KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
        add_le_add
          (gramAfterRight_traceNorm_le_kummer lam alpha hlam ha B)
          (gramAfterRight_traceNorm_le_kummer lam alpha hlam ha D)
    _ = (‖B‖ ^ 2 + ‖D‖ ^ 2) *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRight_basisTrace_eq_rowMass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRightPair_traceNorm_add
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramAfterRightPair_traceNorm_le_kummer

end GegenbauerFock.GeneralUltrasphericalFock
