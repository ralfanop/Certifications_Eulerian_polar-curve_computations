import GegenbauerFock.TwoSidedGramZeroNonEigen
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — proper, nonsurjective ranges of both true Grams

For the genuine ultraspherical analysis operator C with λ,α>0,
both C†C and CC† have proper ranges. For the source Gram, injectivity
of C makes C†C injective, while zero is in its spectrum, excluding
a continuous inverse and therefore surjectivity. For the output
Gram, its image is contained in the proper image of C.

This does not assert the Grams have a nonzero null vector.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

theorem gram_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (gram lam alpha hlam ha) := by
  intro hsurj
  have hker : (gram lam alpha hlam ha).ker = ⊥ := by
    change ((C lam alpha hlam ha).adjoint ∘L
      (C lam alpha hlam ha)).ker = ⊥
    rw [ContinuousLinearMap.ker_adjoint_comp_self]
    exact LinearMap.ker_eq_bot.mpr (C_injective lam alpha hlam ha)
  have hbij : Function.Bijective (gram lam alpha hlam ha) :=
    ⟨LinearMap.ker_eq_bot.mp hker, hsurj⟩
  have hunit : IsUnit (gram lam alpha hlam ha) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr hbij
  exact (spectrum.zero_mem_iff ℂ).mp
    (gram_zero_mem_spectrum lam alpha hlam ha) hunit

theorem outputGram_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (outputGram lam alpha hlam ha) := by
  intro hsurj
  apply C_not_surjective lam alpha hlam ha
  intro F
  obtain ⟨G, hG⟩ := hsurj F
  refine ⟨C_adjoint lam alpha hlam ha G, ?_⟩
  change C lam alpha hlam ha (C_adjoint lam alpha hlam ha G) = F at hG
  exact hG

theorem two_sided_gram_not_surjective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ Function.Surjective (gram lam alpha hlam ha) ∧
      ¬ Function.Surjective (outputGram lam alpha hlam ha) :=
  ⟨gram_not_surjective lam alpha hlam ha,
   outputGram_not_surjective lam alpha hlam ha⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_not_surjective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_not_surjective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_gram_not_surjective

end GegenbauerFock.GeneralUltrasphericalFock
