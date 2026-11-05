import GegenbauerFock.UnconditionalSourceSpectralCompleteness
import GegenbauerFock.OutputEntireCoefficientUniqueness
import GegenbauerFock.SingularEigenspaceLinearEquiv

/-!
# V007 — two-sided complete nonzero singular spectral theorem

This is a consolidation of independently certified results for the
genuine Gegenbauer--Fock operator C, not a finite-matrix analogue.
Both the source and coefficient-side Hilbert adjoint kernels vanish;
both compact positive Grams have complete nonzero eigenspace systems.

The nonzero eigenvalues carry linearly equivalent eigenspaces of equal
finite multiplicity. This file never asserts surjectivity of C:
a compact operator with dense range need not be surjective.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine Gegenbauer--Fock transform and its Hilbert adjoint
are both injective for all strictly positive parameters. -/
theorem C_two_sided_injectivity
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C lam alpha hlam ha) ∧
      Function.Injective (C_adjoint lam alpha hlam ha) :=
  ⟨C_injective lam alpha hlam ha,
   C_adjoint_injective_unconditional lam alpha hlam ha⟩

/-- Both zero eigenvalue sectors of the true source/output compact
Grams are trivial, without auxiliary density premises. -/
theorem two_sided_zero_eigenspaces_bot
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap (0 : ℂ) =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      eigenspace (outputGram lam alpha hlam ha).toLinearMap (0 : ℂ) =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
  ⟨gramIntegralOperator_zero_eigenspace_bot lam alpha hlam ha,
   outputGram_zero_eigenspace_bot_unconditional lam alpha hlam ha⟩

/-- Simultaneous complete nonzero singular spectral systems in the
original ultraspherical L² and the full Fock coefficient Hilbert space.
Completeness means dense span, not a claim of C surjectivity. -/
theorem two_sided_nonzero_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((⨆ mu : ℂ,
        if mu = 0 then
          (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))
        else
          eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)ᗮ =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam)))) ∧
      ((⨆ mu : ℂ,
        if mu = 0 then
          (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)
        else
          eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)) :=
  ⟨gramIntegralOperator_nonzero_eigenspaces_complete lam alpha hlam ha,
   outputGram_nonzero_eigenspaces_complete_unconditional lam alpha hlam ha⟩

/-- All nonzero singular spectral multiplicities agree across the two
true Hilbert spaces; no global source/target isomorphism is claimed. -/
theorem two_sided_nonzero_spectral_multiplicities_eq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    Module.finrank ℂ (eigenspace (gram lam alpha hlam ha).toLinearMap mu) =
      Module.finrank ℂ (eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) :=
  C_nonzero_eigenspace_finrank_eq lam alpha hlam ha mu hmu

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_two_sided_injectivity
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_zero_eigenspaces_bot
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_nonzero_eigenspaces_complete
#print axioms GegenbauerFock.GeneralUltrasphericalFock.two_sided_nonzero_spectral_multiplicities_eq

end GegenbauerFock.GeneralUltrasphericalFock
