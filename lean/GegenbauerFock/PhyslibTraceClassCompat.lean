import GegenbauerFock.PositiveTraceClassBridge
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# V007: source-compatible Physlib infinite-dimensional trace-class bridge

The upstream PhyslibAlpha project defines
`ProbabilisticTheory.IsTraceClass` and
`ProbabilisticTheory.traceNorm` in
`PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Basic.lean`
(author: Tom Ole Diem; Apache-2.0). The following exact foundational
definitions are selectively ported here to V007's fixed Lean
v4.35.0-rc3 and Mathlib SHA 0272bbe, rather than adding Physlib as a
dependency and changing the locked Mathlib/toolchain.

This minimal compatibility layer is NOT the full upstream Physlib
library: its generic Banach-space and two-sided ideal results are
separate obligations. The results below prove *actual* membership of
the concrete positive Gram operator in this source-compatible S₁
class, with its trace norm equal to the certified Kummer value.
-/

noncomputable section

namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Source-compatible port of PhyslibAlpha's `IsTraceClass` definition:
summability of the diagonal of the genuine CFC absolute value on one
complete Hilbert basis. It is not merely a positive nuclear witness. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ (w : Set H) (b : HilbertBasis w ℂ H),
    Summable (fun i => (inner ℂ (b i) (CFC.abs T (b i))).re)

/-- Source-compatible port of PhyslibAlpha's `traceNorm`, with an
actual trace-class witness and the functional-calculus absolute value. -/
noncomputable def traceNorm (T : H →L[ℂ] H) (h : IsTraceClass T) : ℝ :=
  ∑' i : h.choose,
    (inner ℂ (h.choose_spec.choose i)
      (CFC.abs T (h.choose_spec.choose i))).re

/-- Conjugate symmetry of complex inner products after taking real parts. -/
private theorem re_inner_swap (x y : H) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  calc
    (inner ℂ x y).re = (star (inner ℂ y x)).re := by
      exact congrArg Complex.re (inner_conj_symm (𝕜 := ℂ) x y).symm
    _ = (inner ℂ y x).re := by simp

/-- For nonnegative operators the genuine CFC absolute value equals
the operator, so a summable diagonal proves trace-class membership. -/
theorem isTraceClass_of_nonneg_of_summable
    (T : H →L[ℂ] H) (hT : 0 ≤ T)
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hs : Summable (fun i : w =>
      (inner ℂ (b i) (T (b i))).re)) :
    IsTraceClass T := by
  refine ⟨w, b, ?_⟩
  simpa only [CFC.abs_of_nonneg T hT] using hs

/-- The source-compatible trace norm of a positive operator is the
diagonal trace in the witness Hilbert basis. -/
theorem traceNorm_eq_diagonal_of_nonneg
    (T : H →L[ℂ] H) (hT : 0 ≤ T) (h : IsTraceClass T) :
    traceNorm T h =
      ∑' i : h.choose,
        (inner ℂ (h.choose_spec.choose i)
          (T (h.choose_spec.choose i))).re := by
  simp only [traceNorm, CFC.abs_of_nonneg T hT]

#print axioms ProbabilisticTheory.isTraceClass_of_nonneg_of_summable
#print axioms ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg

end ProbabilisticTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Positivity of the full, genuinely bounded ultraspherical Gram
operator in Mathlib's ordered C*-algebra of Hilbert-space endomorphisms. -/
theorem gram_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    0 ≤ gram lam alpha hlam ha := by
  change 0 ≤ (C lam alpha hlam ha).adjoint.comp (C lam alpha hlam ha)
  exact (ContinuousLinearMap.nonneg_iff_isPositive).2
    (ContinuousLinearMap.isPositive_adjoint_comp_self
      (C lam alpha hlam ha))

/-- Exact, unconditional Physlib-compatible S₁ membership of
the non-finite-rank Gram C†C, using the genuine CFC absolute value
and all pre-certified arbitrary-source-basis HS energy identities. -/
theorem gram_isTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.IsTraceClass (gram lam alpha hlam ha) := by
  let H := Lp ℂ 2 (Ultraspherical.measure lam)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have hG := gram_nonneg lam alpha hlam ha
  have hs : Summable (fun i : w =>
      (inner ℂ (b i) (gram lam alpha hlam ha (b i))).re) := by
    have hC : Summable (fun i : w =>
        ‖C lam alpha hlam ha (b i)‖ ^ 2) :=
      C_isHilbertSchmidt lam alpha hlam ha b
    apply hC.congr
    intro i
    have hnorm := HilbertGram.gram_norm_sq (C lam alpha hlam ha) (b i)
    have hsym :
        (inner ℂ (gram lam alpha hlam ha (b i)) (b i)).re =
        (inner ℂ (b i) (gram lam alpha hlam ha (b i))).re :=
      ProbabilisticTheory.re_inner_swap
        (gram lam alpha hlam ha (b i)) (b i)
    exact hnorm.trans hsym
  exact ProbabilisticTheory.isTraceClass_of_nonneg_of_summable
    (gram lam alpha hlam ha) hG b hs

/-- The actual Physlib-compatible TRACE NORM of C†C is exactly
the Gamma-corrected unregularized Kummer hypergeometric value. -/
theorem gram_traceNorm_eq_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.traceNorm (gram lam alpha hlam ha)
      (gram_isTraceClass lam alpha hlam ha) =
      KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  let G := gram lam alpha hlam ha
  let h := gram_isTraceClass lam alpha hlam ha
  have hn : 0 ≤ G := gram_nonneg lam alpha hlam ha
  rw [ProbabilisticTheory.traceNorm_eq_diagonal_of_nonneg G hn h]
  calc
    (∑' i : h.choose,
      (inner ℂ (h.choose_spec.choose i)
        (G (h.choose_spec.choose i))).re) =
      ∑' i : h.choose,
        (inner ℂ (G (h.choose_spec.choose i))
          (h.choose_spec.choose i)).re := by
        apply tsum_congr
        intro i
        exact ProbabilisticTheory.re_inner_swap
          (h.choose_spec.choose i) (G (h.choose_spec.choose i))
    _ = KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) :=
      gram_sourceBasis_trace_eq_kummer lam alpha hlam ha h.choose_spec.choose

/-- Equivalence with V007's certified nuclear rank-one mass,
in a proper trace-norm model matching Physlib's source definition. -/
theorem gram_traceNorm_eq_positiveNuclearMass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ProbabilisticTheory.traceNorm (gram lam alpha hlam ha)
      (gram_isTraceClass lam alpha hlam ha) =
        ∑' n : ℕ, ‖gramNuclearTerm lam alpha hlam ha n‖ := by
  rw [gram_traceNorm_eq_kummer lam alpha hlam ha]
  exact (gramNuclearMass_eq_kummerSeries lam alpha hlam ha).symm

/-- Exact Gamma-normalized Mathlib complex hypergeometric value of the
genuine CFC trace norm of the positive ultraspherical Gram. -/
theorem gram_traceNorm_eq_mathlibRegularizedKummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((ProbabilisticTheory.traceNorm (gram lam alpha hlam ha)
      (gram_isTraceClass lam alpha hlam ha)) : ℂ) =
      Complex.Gamma (((lam + 1 : ℝ) : ℂ)) *
        KummerCoefficients.mathlibRegularizedKummer lam
          (((1 / (4 * alpha) : ℝ) : ℂ)) := by
  rw [gram_traceNorm_eq_kummer lam alpha hlam ha]
  exact KummerCoefficients.kummerSeries_eq_gamma_mul_mathlibRegularized
    lam (1 / (4 * alpha)) hlam

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_nonneg
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_isTraceClass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_traceNorm_eq_kummer
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_traceNorm_eq_positiveNuclearMass
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_traceNorm_eq_mathlibRegularizedKummer

end GegenbauerFock.GeneralUltrasphericalFock
