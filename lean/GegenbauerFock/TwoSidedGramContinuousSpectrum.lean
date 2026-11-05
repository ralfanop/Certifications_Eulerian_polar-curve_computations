import GegenbauerFock.TwoSidedGramNonclosedRange
import GegenbauerFock.TwoSidedGramZeroNonEigen

/-!
# V007 — zero belongs to the continuous spectrum of both true Gram operators

For a bounded Hilbert-space endomorphism, zero is in the continuous
spectrum precisely when the operator is injective, has dense image,
and is not onto.  The explicit spectral membership is included for
an independently auditable statement.

The two Gegenbauer–Fock Gram operators act on distinct Hilbert
spaces.  Neither has a zero eigenvector; neither has a bounded inverse.
No identification of the two spaces is used.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The standard zero-point continuous-spectrum criterion, stated
using the actual operator spectrum, kernel and dense proper range.
The final clause prevents the residual/point-spectrum confusion. -/
def IsContinuousSpectralPointAtZero {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) : Prop :=
  (0 : ℂ) ∈ spectrum ℂ T ∧
  T.ker = ⊥ ∧
  T.range.topologicalClosure = ⊤ ∧
  ¬ Function.Surjective T

/-- Zero is in the continuous spectrum of the source Gram C†C
on the genuine ultraspherical L² space. -/
theorem source_gram_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsContinuousSpectralPointAtZero (gram lam alpha hlam ha) := by
  unfold IsContinuousSpectralPointAtZero
  refine ⟨gram_zero_mem_spectrum lam alpha hlam ha, ?_,
    gram_dense_range lam alpha hlam ha,
    gram_not_surjective lam alpha hlam ha⟩
  change ((C lam alpha hlam ha).adjoint ∘L
    (C lam alpha hlam ha)).ker = ⊥
  rw [ContinuousLinearMap.ker_adjoint_comp_self]
  exact LinearMap.ker_eq_bot.mpr (C_injective lam alpha hlam ha)

/-- Zero is in the continuous spectrum of the output Gram CC†
on the full Fock-coefficient Hilbert space. -/
theorem output_gram_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsContinuousSpectralPointAtZero (outputGram lam alpha hlam ha) := by
  unfold IsContinuousSpectralPointAtZero
  refine ⟨outputGram_zero_mem_spectrum lam alpha hlam ha, ?_,
    outputGram_dense_range lam alpha hlam ha,
    outputGram_not_surjective lam alpha hlam ha⟩
  change ((C lam alpha hlam ha).comp
    (C lam alpha hlam ha).adjoint).ker = ⊥
  rw [ContinuousLinearMap.ker_self_comp_adjoint]
  exact LinearMap.ker_eq_bot.mpr
    (C_adjoint_injective_unconditional lam alpha hlam ha)

/-- The two Grams have zero in their continuous (not point or residual)
spectra simultaneously, in their respective Hilbert spaces. -/
theorem two_sided_gram_zero_continuous_spectrum
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsContinuousSpectralPointAtZero (gram lam alpha hlam ha) ∧
      IsContinuousSpectralPointAtZero (outputGram lam alpha hlam ha) :=
  ⟨source_gram_zero_continuous_spectrum lam alpha hlam ha,
   output_gram_zero_continuous_spectrum lam alpha hlam ha⟩

/-- Stronger geometric consequence: both continuous-spectrum ranges
are dense and nonclosed, but neither is the full Hilbert space. -/
theorem two_sided_continuous_zero_nonclosed_ranges
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (¬ IsClosed ((gram lam alpha hlam ha).range :
      Set (Lp ℂ 2 (Ultraspherical.measure lam)))) ∧
    (¬ IsClosed ((outputGram lam alpha hlam ha).range :
      Set InfiniteAnalysis.FockCoefficients)) :=
  two_sided_gram_nonclosed_ranges lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.source_gram_zero_continuous_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.output_gram_zero_continuous_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_zero_continuous_spectrum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_continuous_zero_nonclosed_ranges

end GegenbauerFock.GeneralUltrasphericalFock
