import GegenbauerFock.RectangularHSAdjointTrace

/-!
# V007 — equality of the two genuine CFC Gram trace norms

For a rectangular Hilbert–Schmidt operator T : E → F between
arbitrary complete complex Hilbert spaces, the source Gram T†T
and target Gram TT† have the same *actual Physlib-compatible*
CFC trace norm. This is not merely equality of two nuclear proxies.

The statement accepts any true S₁ witnesses for the two Grams:
their selected Hilbert bases may differ. The proof uses positivity,
both Gram identities, rectangular Parseval/Tonelli and the precise
witness-selected diagonal definition. No full S₁ Banach space is
assumed or silently introduced.

Until the exact-sha build/audit is green this is candidate source.
-/

noncomputable section

namespace GegenbauerFock.HilbertSchmidtBasis

open scoped InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

private theorem swap_real_inner
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x y : H) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- Equality of both Gram trace norms, even when the two
CFC-positive diagonal summability witnesses use unrelated bases. -/
theorem traceNorm_adjoint_comp_eq_comp_adjoint
    (T : E →L[ℂ] F) (hT : IsHS T)
    (hSrc : ProbabilisticTheory.IsTraceClass (T.adjoint.comp T))
    (hDst : ProbabilisticTheory.IsTraceClass (T.comp T.adjoint)) :
    ProbabilisticTheory.traceNorm (T.adjoint.comp T) hSrc =
      ProbabilisticTheory.traceNorm (T.comp T.adjoint) hDst := by
  have hpSrc : 0 ≤ T.adjoint.comp T :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hpDst : 0 ≤ T.comp T.adjoint := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using
      ((ContinuousLinearMap.nonneg_iff_isPositive).2
        (ContinuousLinearMap.isPositive_adjoint_comp_self T.adjoint))
  rw [ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg
        (T.adjoint.comp T) hpSrc hSrc,
      ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg
        (T.comp T.adjoint) hpDst hDst]
  calc
    (∑' i : hSrc.choose,
       (inner ℂ (hSrc.choose_spec.choose i)
         ((T.adjoint.comp T) (hSrc.choose_spec.choose i))).re) =
      ∑' i : hSrc.choose, ‖T (hSrc.choose_spec.choose i)‖ ^ 2 := by
        apply tsum_congr
        intro i
        have hn := GegenbauerFock.HilbertGram.gram_norm_sq T
          (hSrc.choose_spec.choose i)
        have hn' : ‖T (hSrc.choose_spec.choose i)‖ ^ 2 =
            (inner ℂ ((T.adjoint.comp T) (hSrc.choose_spec.choose i))
              (hSrc.choose_spec.choose i)).re := by
          simpa only [GegenbauerFock.HilbertGram.gram] using hn
        exact (swap_real_inner
          (hSrc.choose_spec.choose i)
          ((T.adjoint.comp T) (hSrc.choose_spec.choose i))).trans hn'.symm
    _ = ∑' j : hDst.choose,
          ‖T.adjoint (hDst.choose_spec.choose j)‖ ^ 2 :=
        (hasSum_adjoint_energy_rectangular
          T hSrc.choose_spec.choose hDst.choose_spec.choose
          (hT hSrc.choose_spec.choose)).tsum_eq.symm
    _ = ∑' j : hDst.choose,
          (inner ℂ (hDst.choose_spec.choose j)
            ((T.comp T.adjoint) (hDst.choose_spec.choose j))).re := by
        apply tsum_congr
        intro j
        have hn := GegenbauerFock.HilbertGram.gram_norm_sq T.adjoint
          (hDst.choose_spec.choose j)
        have hn' : ‖T.adjoint (hDst.choose_spec.choose j)‖ ^ 2 =
            (inner ℂ ((T.comp T.adjoint) (hDst.choose_spec.choose j))
              (hDst.choose_spec.choose j)).re := by
          simpa only [GegenbauerFock.HilbertGram.gram,
            ContinuousLinearMap.adjoint_adjoint] using hn
        exact hn'.trans (swap_real_inner
          ((T.comp T.adjoint) (hDst.choose_spec.choose j))
          (hDst.choose_spec.choose j))

#print axioms GegenbauerFock.HilbertSchmidtBasis.traceNorm_adjoint_comp_eq_comp_adjoint

end GegenbauerFock.HilbertSchmidtBasis
