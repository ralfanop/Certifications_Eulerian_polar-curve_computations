import GegenbauerFock.TwoSidedGramContinuousSpectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — general Hilbert-space criterion for zero in the continuous spectrum

This removes the specific Gegenbauer–Fock kernel from the mechanism:
a bounded selfadjoint complex Hilbert operator with trivial kernel
and spectral zero has dense, proper range. Hence zero is in the
continuous spectrum and not the residual or point spectrum.

The criterion applies separately to the source and output Grams;
it does not identify their Hilbert spaces.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Injectivity of a bounded selfadjoint Hilbert-space operator forces
its image to be dense, even without a compactness assumption. -/
theorem selfadjoint_dense_range_of_injective
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H)
    (hself : T.adjoint = T) (hinj : Function.Injective T) :
    T.range.topologicalClosure = (⊤ : Submodule ℂ H) := by
  have hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  apply (Submodule.topologicalClosure_eq_top_iff).2
  rw [T.orthogonal_range, hself, hker]

/-- Abstract characterization: for an injective bounded selfadjoint
Hilbert-space operator, spectral zero necessarily has dense, proper
range (continuous spectrum). -/
theorem selfadjoint_zero_continuous_of_spectral_not_eigen
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H)
    (hself : T.adjoint = T)
    (hinj : Function.Injective T)
    (hzero : (0 : ℂ) ∈ spectrum ℂ T) :
    IsContinuousSpectralPointAtZero T := by
  have hsurj : ¬ Function.Surjective T := by
    intro hs
    have hunit : IsUnit T :=
      ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hs⟩
    exact (spectrum.zero_mem_iff ℂ).mp hzero hunit
  exact ⟨hzero, LinearMap.ker_eq_bot.mpr hinj,
    selfadjoint_dense_range_of_injective T hself hinj, hsurj⟩

/-- General abstract criterion specialized to the true L² source Gram. -/
theorem source_gram_zero_continuous_by_selfadjoint_criterion
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsContinuousSpectralPointAtZero (gram lam alpha hlam ha) := by
  apply selfadjoint_zero_continuous_of_spectral_not_eigen
    (gram lam alpha hlam ha)
    (gram_selfadjoint lam alpha hlam ha)
  · exact LinearMap.ker_eq_bot.mp
      (source_gram_zero_continuous_spectrum lam alpha hlam ha).2.1
  · exact gram_zero_mem_spectrum lam alpha hlam ha

/-- The independent coefficient-Hilbert-space Gram obeys the same
abstract selfadjoint spectral criterion. -/
theorem output_gram_zero_continuous_by_selfadjoint_criterion
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsContinuousSpectralPointAtZero (outputGram lam alpha hlam ha) := by
  apply selfadjoint_zero_continuous_of_spectral_not_eigen
    (outputGram lam alpha hlam ha)
    (outputGram_selfadjoint lam alpha hlam ha)
  · exact LinearMap.ker_eq_bot.mp
      (output_gram_zero_continuous_spectrum lam alpha hlam ha).2.1
  · exact outputGram_zero_mem_spectrum lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.selfadjoint_dense_range_of_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.selfadjoint_zero_continuous_of_spectral_not_eigen
#print axioms GegenbauerFock.GeneralUltrasphericalFock.source_gram_zero_continuous_by_selfadjoint_criterion
#print axioms GegenbauerFock.GeneralUltrasphericalFock.output_gram_zero_continuous_by_selfadjoint_criterion

end GegenbauerFock.GeneralUltrasphericalFock
