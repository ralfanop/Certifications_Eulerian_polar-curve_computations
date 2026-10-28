import GegenbauerFock.HSRowBasisGeneral
import GegenbauerFock.PhyslibTraceClassCompat
import GegenbauerFock.PositiveNuclearConjugation

/-!
# V007: general Hilbert–Schmidt Gram trace-class and ideal inequality

For any complete complex Hilbert source E, any bounded map
T : E → ℓ²(ℕ,ℂ) whose canonical coefficient functionals are
square-summable has a positive trace-class Gram T†T in the
**source-compatible PhyslibAlpha CFC.abs S₁ predicate**.

Its actual Physlib-compatible trace norm is the sum of squared row
norms, and bounded precomposition B : D → E satisfies the sharp
source-side quadratic Schatten-type ideal inequality

    ||(T B)† (T B)||₁ ≤ ||B||² ||T† T||₁.

All Hilbert spaces E,D may be infinite-dimensional. No new axiom,
finite cutoff, basis hypothesis or replacement of pinned Mathlib.
This is a positive Gram ideal statement, NOT a claim that the full
Physlib Banach class and its general ATB two-sided-ideal API have
already been imported.
-/

noncomputable section

namespace GegenbauerFock.FockEnergy

variable {E D : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]

private theorem gram_diag_re_eq_norm_sq
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients) (x : E) :
    (inner ℂ x (T.adjoint.comp T x)).re = ‖T x‖ ^ 2 := by
  calc
    (inner ℂ x (T.adjoint.comp T x)).re =
        (inner ℂ (T.adjoint.comp T x) x).re := by
          calc
            (inner ℂ x (T.adjoint.comp T x)).re =
                (star (inner ℂ (T.adjoint.comp T x) x)).re := by
                  exact congrArg Complex.re
                    (inner_conj_symm (𝕜 := ℂ) x (T.adjoint.comp T x)).symm
            _ = (inner ℂ (T.adjoint.comp T x) x).re := by
                  simp only [Complex.star_def, Complex.conj_re]
    _ = ‖T x‖ ^ 2 := (HilbertGram.gram_norm_sq T x).symm

/-- Norm-squared row estimate under bounded precomposition between
possibly distinct complex Hilbert source spaces. -/
private theorem row_comp_norm_sq_le_between
    (r : E →L[ℂ] ℂ) (B : D →L[ℂ] E) :
    ‖r.comp B‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖r‖ ^ 2 := by
  calc
    ‖r.comp B‖ ^ 2 ≤ (‖r‖ * ‖B‖) ^ 2 := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le r B
    _ = ‖B‖ ^ 2 * ‖r‖ ^ 2 := by ring

/-- Every square-summable-row operator has a TRUE trace-class
positive Gram, in the CFC.abs summability notion of Physlib. -/
theorem gram_isTraceClass_of_summableRows
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2)) :
    ProbabilisticTheory.IsTraceClass (T.adjoint.comp T) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
  have hPos : 0 ≤ T.adjoint.comp T :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  have hs : Summable (fun i : w =>
      (inner ℂ (b i) (T.adjoint.comp T (b i))).re) := by
    exact (summableRows_iff_sourceBasis_energy T hrows b).1.congr
      (fun i => (gram_diag_re_eq_norm_sq T (b i)).symm)
  exact ProbabilisticTheory.isTraceClass_of_nonneg_of_summable
    (T.adjoint.comp T) hPos b hs

/-- The full trace norm of the positive Gram equals the exact
basis-independent Hilbert--Schmidt row mass for arbitrary T. -/
theorem gram_traceNorm_eq_rows
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2)) :
    ProbabilisticTheory.traceNorm (T.adjoint.comp T)
      (gram_isTraceClass_of_summableRows T hrows) =
        ∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2 := by
  let h := gram_isTraceClass_of_summableRows T hrows
  have hPos : 0 ≤ T.adjoint.comp T :=
    (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self T)
  rw [ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg
      (T.adjoint.comp T) hPos h]
  calc
    (∑' i : h.choose,
       (inner ℂ (h.choose_spec.choose i)
         (T.adjoint.comp T (h.choose_spec.choose i))).re) =
        ∑' i : h.choose, ‖T (h.choose_spec.choose i)‖ ^ 2 := by
          apply tsum_congr
          intro i
          exact gram_diag_re_eq_norm_sq T (h.choose_spec.choose i)
    _ = ∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2 :=
      (summableRows_iff_sourceBasis_energy
        T hrows h.choose_spec.choose).2

/-- The canonical Fock rows of T B are exactly the original Fock
rows precomposed by B. The two spaces need not coincide. -/
theorem row_comp_right
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (B : D →L[ℂ] E) (n : ℕ) :
    SummableRowsCompact.row (T.comp B) n =
      (SummableRowsCompact.row T n).comp B := by
  ext x
  rfl

/-- The square-summable-row class is an ideal under arbitrary bounded
source precomposition, including between distinct Hilbert spaces. -/
theorem rows_summable_comp_right
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    (B : D →L[ℂ] E) :
    Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) := by
  have hs : Summable (fun n : ℕ =>
      ‖(SummableRowsCompact.row T n).comp B‖ ^ 2) := by
    apply Summable.of_nonneg_of_le
    · intro n
      exact sq_nonneg _
    · intro n
      exact (row_comp_norm_sq_le_between
        (SummableRowsCompact.row T n) B)
    · exact hrows.mul_left (‖B‖ ^ 2)
  exact hs.congr (fun n => by rw [row_comp_right T B n])

/-- Exact basis-independent Schatten-S₂ energy under right
composition, with the sharp operator-norm-squared estimate. -/
theorem rowEnergy_comp_right_le
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    (B : D →L[ℂ] E) :
    (∑' n : ℕ, ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) ≤
      ‖B‖ ^ 2 * (∑' n : ℕ,
        ‖SummableRowsCompact.row T n‖ ^ 2) := by
  have hs : Summable (fun n : ℕ =>
      ‖(SummableRowsCompact.row T n).comp B‖ ^ 2) := by
    exact (rows_summable_comp_right T hrows B).congr
      (fun n => by rw [row_comp_right T B n])
  calc
    (∑' n : ℕ, ‖SummableRowsCompact.row (T.comp B) n‖ ^ 2) =
        ∑' n : ℕ, ‖(SummableRowsCompact.row T n).comp B‖ ^ 2 := by
          apply tsum_congr
          intro n
          rw [row_comp_right T B n]
    _ ≤ ‖B‖ ^ 2 * (∑' n : ℕ,
        ‖SummableRowsCompact.row T n‖ ^ 2) := by
          have hbound (n : ℕ) :
              ‖(SummableRowsCompact.row T n).comp B‖ ^ 2 ≤
                ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 :=
              row_comp_norm_sq_le_between
                (SummableRowsCompact.row T n) B
          calc
            (∑' n : ℕ, ‖(SummableRowsCompact.row T n).comp B‖ ^ 2) ≤
                ∑' n : ℕ,
                  ‖B‖ ^ 2 * ‖SummableRowsCompact.row T n‖ ^ 2 :=
              hs.tsum_le_tsum hbound (hrows.mul_left (‖B‖ ^ 2))
            _ = ‖B‖ ^ 2 *
                (∑' n : ℕ, ‖SummableRowsCompact.row T n‖ ^ 2) :=
              tsum_mul_left

/-- Actual Physlib-compatible trace-norm estimate for the
conjugated positive Gram (T B)†(T B). -/
theorem gram_traceNorm_comp_right_le
    (T : E →L[ℂ] InfiniteAnalysis.FockCoefficients)
    (hrows : Summable (fun n : ℕ =>
      ‖SummableRowsCompact.row T n‖ ^ 2))
    (B : D →L[ℂ] E) :
    ProbabilisticTheory.traceNorm
      ((T.comp B).adjoint.comp (T.comp B))
      (gram_isTraceClass_of_summableRows
        (T.comp B) (rows_summable_comp_right T hrows B)) ≤
      ‖B‖ ^ 2 *
        ProbabilisticTheory.traceNorm (T.adjoint.comp T)
          (gram_isTraceClass_of_summableRows T hrows) := by
  rw [gram_traceNorm_eq_rows
    (T.comp B) (rows_summable_comp_right T hrows B)]
  rw [gram_traceNorm_eq_rows T hrows]
  exact rowEnergy_comp_right_le T hrows B

#print axioms GegenbauerFock.FockEnergy.gram_isTraceClass_of_summableRows
#print axioms GegenbauerFock.FockEnergy.gram_traceNorm_eq_rows
#print axioms GegenbauerFock.FockEnergy.rows_summable_comp_right
#print axioms GegenbauerFock.FockEnergy.rowEnergy_comp_right_le
#print axioms GegenbauerFock.FockEnergy.gram_traceNorm_comp_right_le

end GegenbauerFock.FockEnergy
