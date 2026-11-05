import GegenbauerFock.TwoSidedGramNotSurjective
import GegenbauerFock.OutputGramSpectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# V007 — both exact Grams have proper dense ranges

The genuine positive compact source and coefficient Fock Grams
G=C†C and H=CC† are injective, selfadjoint and nonsurjective.
Their ranges are nevertheless dense, since the orthogonal
complement of the range of a selfadjoint Hilbert operator
coincides with its nullspace, which is zero.

Hence zero belongs to the continuous (rather than point)
spectrum on BOTH genuinely different Hilbert spaces.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem gram_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (gram lam alpha hlam ha).range.topologicalClosure =
      (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  have hker : (gram lam alpha hlam ha).ker = ⊥ := by
    change ((C lam alpha hlam ha).adjoint ∘L
      (C lam alpha hlam ha)).ker = ⊥
    rw [ContinuousLinearMap.ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.mpr (C_injective lam alpha hlam ha)
  apply (Submodule.topologicalClosure_eq_top_iff).2
  rw [(gram lam alpha hlam ha).orthogonal_range,
    gram_selfadjoint lam alpha hlam ha, hker]

theorem outputGram_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (outputGram lam alpha hlam ha).range.topologicalClosure =
      (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  have hker : (outputGram lam alpha hlam ha).ker = ⊥ := by
    change ((C lam alpha hlam ha).comp
      (C lam alpha hlam ha).adjoint).ker = ⊥
    rw [ContinuousLinearMap.ker_self_comp_adjoint]
    exact LinearMap.ker_eq_bot.mpr
      (C_adjoint_injective_unconditional lam alpha hlam ha)
  apply (Submodule.topologicalClosure_eq_top_iff).2
  rw [(outputGram lam alpha hlam ha).orthogonal_range,
    outputGram_selfadjoint lam alpha hlam ha, hker]

/-- Both Grams have dense image that is NOT all of their respective
Hilbert spaces (equivalently, zero lies in the continuous spectrum). -/
theorem two_sided_gram_proper_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((gram lam alpha hlam ha).range.topologicalClosure =
       (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
       ¬ Function.Surjective (gram lam alpha hlam ha)) ∧
    ((outputGram lam alpha hlam ha).range.topologicalClosure =
       (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) ∧
       ¬ Function.Surjective (outputGram lam alpha hlam ha)) :=
  ⟨⟨gram_dense_range lam alpha hlam ha, gram_not_surjective lam alpha hlam ha⟩,
   ⟨outputGram_dense_range lam alpha hlam ha,
      outputGram_not_surjective lam alpha hlam ha⟩⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_dense_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_proper_dense_range

end GegenbauerFock.GeneralUltrasphericalFock
