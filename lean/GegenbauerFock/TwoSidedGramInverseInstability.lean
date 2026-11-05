import GegenbauerFock.TwoSidedGramContinuousSpectrum
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — the two exact Gram inverses are unbounded on their ranges

Both Gram operators G=C†C and H=CC† are injective and have dense,
proper, nonclosed ranges in their *different* Hilbert spaces. We
formalize a quantitative obstruction to bounded inversion on each
range: for every finite K≥0 there is an actual input whose norm
is strictly larger than K times the Gram-output norm. This is stronger
than merely asserting that zero is not in the resolvent.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Abstract closed-range obstruction to an inverse stability bound.
No inverse map is asserted to be a total bounded endomorphism. -/
private theorem inverse_instability_of_nonclosed_range
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H)
    (hinj : Function.Injective T)
    (hnotclosed : ¬ IsClosed (T.range : Set H))
    (K : ℝ≥0) :
    ∃ x : H, (K : ℝ) * ‖T x‖ < ‖x‖ := by
  have hnotanti : ¬ AntilipschitzWith K T := by
    intro hanti
    exact hnotclosed
      ((T.isClosed_range_iff_antilipschitz_of_injective hinj).mpr
        ⟨K, hanti⟩)
  rw [antilipschitzWith_iff_le_mul_dist] at hnotanti
  push_neg at hnotanti
  obtain ⟨f, g, hfg⟩ := hnotanti
  refine ⟨f - g, ?_⟩
  rw [map_sub]
  simpa only [dist_eq_norm] using hfg

/-- The source Gram inverse, defined on Ran(C†C), cannot satisfy
any global finite Lipschitz bound. -/
theorem sourceGram_inverse_unbounded_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      (K : ℝ) * ‖gram lam alpha hlam ha f‖ < ‖f‖ := by
  have hzero :
      (gram lam alpha hlam ha).ker =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    have hspec := source_gram_zero_continuous_spectrum lam alpha hlam ha
    exact hspec.2.1
  exact inverse_instability_of_nonclosed_range
    (gram lam alpha hlam ha)
    (LinearMap.ker_eq_bot.mp hzero)
    (gram_range_not_closed lam alpha hlam ha) K

/-- The output Gram inverse, defined on Ran(CC†), cannot satisfy
any global finite Lipschitz bound. -/
theorem outputGram_inverse_unbounded_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ F : InfiniteAnalysis.FockCoefficients,
      (K : ℝ) * ‖outputGram lam alpha hlam ha F‖ < ‖F‖ := by
  have hzero :
      (outputGram lam alpha hlam ha).ker =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
    have hspec := output_gram_zero_continuous_spectrum lam alpha hlam ha
    exact hspec.2.1
  exact inverse_instability_of_nonclosed_range
    (outputGram lam alpha hlam ha)
    (LinearMap.ker_eq_bot.mp hzero)
    (outputGram_range_not_closed lam alpha hlam ha) K

/-- Both actual Hilbert-space Gram inverse estimates fail for every
chosen finite K; source and target are not identified. -/
theorem two_sided_gram_inverse_unbounded_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    (∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      (K : ℝ) * ‖gram lam alpha hlam ha f‖ < ‖f‖) ∧
    (∃ F : InfiniteAnalysis.FockCoefficients,
      (K : ℝ) * ‖outputGram lam alpha hlam ha F‖ < ‖F‖) :=
  ⟨sourceGram_inverse_unbounded_on_range lam alpha hlam ha K,
   outputGram_inverse_unbounded_on_range lam alpha hlam ha K⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.sourceGram_inverse_unbounded_on_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_inverse_unbounded_on_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_inverse_unbounded_on_range

end GegenbauerFock.GeneralUltrasphericalFock
