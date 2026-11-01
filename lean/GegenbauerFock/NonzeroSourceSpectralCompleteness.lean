import GegenbauerFock.GramSpectralKernel
import GegenbauerFock.GramSpectralTheorem
import GegenbauerFock.UltrasphericalPolynomialKernel

/-!
# V007 — completion of the nonzero singular source spectrum

The actual compact positive Gram integral operator has a complete
spectral resolution INCLUDING the zero eigenspace. Its zero eigenspace
is precisely the kernel of the true Fock transform C.

This module formalizes a logically separate bridge: if C is injective,
then the nonzero eigenspaces alone have dense span. The bridge takes
either global injectivity or, via the certified kernel/density reduction,
the explicitly stated polynomial-density hypothesis. It does NOT
silently assume polynomial density or declare global injectivity.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Injectivity of the actual Fock map eliminates the zero eigenspace
of its positive compact Gram integral operator. -/
theorem gramIntegralOperator_zero_eigenspace_bot_of_C_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hinj : Function.Injective (C lam alpha hlam ha)) :
    eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap (0 : ℂ) =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  rw [gramIntegralOperator_zero_eigenspace_eq_C_ker]
  exact LinearMap.ker_eq_bot.mpr hinj

/-- Complete nonzero singular source spectrum, conditional only on
injectivity of the real, infinite-dimensional ultraspherical-Fock
operator. Every zero mode has been explicitly removed. -/
theorem gramIntegralOperator_nonzero_eigenspaces_complete_of_C_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hinj : Function.Injective (C lam alpha hlam ha)) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      else
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  have hzero := gramIntegralOperator_zero_eigenspace_bot_of_C_injective
    lam alpha hlam ha hinj
  have hsum :
      (⨆ mu : ℂ,
        if mu = 0 then
          (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
        else
          eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) =
      (⨆ mu : ℂ,
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) := by
    apply iSup_congr
    intro mu
    by_cases hmu : mu = 0
    · subst mu
      simp only [ite_true]
      exact hzero.symm
    · simp only [hmu, ite_false]
  rw [hsum]
  exact gramIntegralOperator_eigenspaces_complete lam alpha hlam ha

/-- Explicit bridge from density of actual L² polynomial Riesz
monomials to completeness of all nonzero Gram source eigenspaces.
The density hypothesis is *not* discharged in this module. -/
theorem gramIntegralOperator_nonzero_eigenspaces_complete_of_monomial_dense
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hdense : (sourceMonomialSpan lam hlam).topologicalClosure = ⊤) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
      else
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  apply gramIntegralOperator_nonzero_eigenspaces_complete_of_C_injective
    lam alpha hlam ha
  exact C_injective_of_monomialSpan_dense lam alpha hlam ha hdense

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_zero_eigenspace_bot_of_C_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_nonzero_eigenspaces_complete_of_C_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_nonzero_eigenspaces_complete_of_monomial_dense

end GegenbauerFock.GeneralUltrasphericalFock
