import GegenbauerFock.PhyslibTraceNormCore
import GegenbauerFock.HSRowBasisGeneral

/-!
# V007 — basis-independent diagonal trace for genuine rank-one Grams

For every bounded complex-linear functional r on an arbitrary complete
complex Hilbert space H, the positive operator r†r has summable
diagonals on EVERY complete Hilbert basis, with the same exact sum
‖r‖². This uses Riesz-Parseval and the genuine adjoint Gram pairing,
not a finite-dimensional surrogate.

The resulting source-compatible Physlib CFC absolute trace norm
is exactly ‖r‖². General basis independence for all S₁ maps, their
unrestricted addition, and trace-norm completeness are separate tasks.
-/ 

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem rankOneGram_re_inner_swap (x y : H) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re :=
      congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by
      simp only [Complex.star_def, Complex.conj_re]

/-- The rank-one Gram of any bounded scalar functional is positive. -/
theorem rankOneGram_nonneg (r : H →L[ℂ] ℂ) :
    0 ≤ GegenbauerFock.HilbertGram.gram r := by
  change 0 ≤ r.adjoint.comp r
  exact (ContinuousLinearMap.nonneg_iff_isPositive).2
    (ContinuousLinearMap.isPositive_adjoint_comp_self r)

/-- Riesz-Parseval identifies the diagonal trace of a rank-one
Gram on EVERY complete Hilbert basis. In particular the value
is independent of this basis. -/
theorem rankOneGram_basisTrace_eq (r : H →L[ℂ] ℂ)
    {ι : Type*} (b : HilbertBasis ι ℂ H) :
    (∑' i : ι,
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re) =
      ‖r‖ ^ 2 := by
  have hdiag (i : ι) :
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re =
        ‖r (b i)‖ ^ 2 := by
    calc
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re =
        (inner ℂ (GegenbauerFock.HilbertGram.gram r (b i)) (b i)).re :=
          rankOneGram_re_inner_swap _ _
      _ = ‖r (b i)‖ ^ 2 :=
        (GegenbauerFock.HilbertGram.gram_norm_sq r (b i)).symm
  calc
    (∑' i : ι,
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re) =
        ∑' i : ι, ‖r (b i)‖ ^ 2 := tsum_congr hdiag
    _ = ‖r‖ ^ 2 :=
      (GegenbauerFock.FockEnergy.functional_basis_energy r b).2

/-- Genuine infinite-dimensional CFC trace-class membership for
every bounded rank-one Gram, with no finite-rank enumeration. -/
theorem rankOneGram_isTraceClass (r : H →L[ℂ] ℂ) :
    IsTraceClass (GegenbauerFock.HilbertGram.gram r) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hdiag (i : w) :
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re =
        ‖r (b i)‖ ^ 2 := by
    calc
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re =
        (inner ℂ (GegenbauerFock.HilbertGram.gram r (b i)) (b i)).re :=
          rankOneGram_re_inner_swap _ _
      _ = ‖r (b i)‖ ^ 2 :=
        (GegenbauerFock.HilbertGram.gram_norm_sq r (b i)).symm
  have hs : Summable (fun i : w =>
      (inner ℂ (b i) (GegenbauerFock.HilbertGram.gram r (b i))).re) :=
    (GegenbauerFock.FockEnergy.functional_basis_energy r b).1.congr
      (fun i => (hdiag i).symm)
  exact isTraceClass_of_nonneg_of_summable
    (GegenbauerFock.HilbertGram.gram r) (rankOneGram_nonneg r) b hs

/-- Exact source-compatible Physlib trace norm of the positive
rank-one Gram; its witness basis is immaterial by Riesz-Parseval. -/
theorem rankOneGram_traceNorm_eq (r : H →L[ℂ] ℂ) :
    traceNorm (GegenbauerFock.HilbertGram.gram r)
      (rankOneGram_isTraceClass r) = ‖r‖ ^ 2 := by
  let h := rankOneGram_isTraceClass r
  change traceNorm (GegenbauerFock.HilbertGram.gram r) h = _
  rw [traceNorm_eq_diagonal_of_nonneg
    (GegenbauerFock.HilbertGram.gram r) (rankOneGram_nonneg r) h]
  exact rankOneGram_basisTrace_eq r h.choose_spec.choose

#print axioms ProbabilisticTheory.rankOneGram_nonneg
#print axioms ProbabilisticTheory.rankOneGram_basisTrace_eq
#print axioms ProbabilisticTheory.rankOneGram_isTraceClass
#print axioms ProbabilisticTheory.rankOneGram_traceNorm_eq

end ProbabilisticTheory
