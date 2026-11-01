import GegenbauerFock.NonzeroOutputSpectralCompleteness
import GegenbauerFock.AnalyticAdjointComplete

/-!
# V007 — exact analytic uniqueness reduction for the output dense-range problem

The actual Hilbert adjoint C† has already been identified with the L²
class of the coherent analytic restriction to the imaginary axis.
This module proves that its kernel is *exactly* the set of coefficient
vectors whose entire reconstruction vanishes almost everywhere for the
actual ultraspherical probability measure.

The analytic uniqueness implication is left explicit. No claim of
unconditional injectivity of C† or dense range is made here.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Vanishing of the actual Hilbert adjoint is equivalent to
almost-everywhere vanishing of the entire coherent reconstruction on
the real ultraspherical coordinate. This is an equality in the genuine
L² space, not an assertion about arbitrary representatives. -/
theorem C_adjoint_eq_zero_iff_analytic_restriction_ae_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : InfiniteAnalysis.FockCoefficients) :
    C_adjoint lam alpha hlam ha F = 0 ↔
      FockAnalyticRestriction.evaluate alpha ha F =ᵐ[Ultraspherical.measure lam]
        (0 : ℝ → ℂ) := by
  rw [FockAnalyticRestriction.adjoint_eq_analytic_restriction]
  change FockAnalyticRestriction.restrictionLp lam alpha hlam ha F = 0 ↔ _
  constructor
  · intro h
    have hz :
        (FockAnalyticRestriction.restrictionLp lam alpha hlam ha F :
          ℝ → ℂ) =ᵐ[Ultraspherical.measure lam] 0 :=
      Lp.eq_zero_iff_ae_eq_zero.mp h
    exact (FockAnalyticRestriction.memLp_evaluate lam alpha hlam ha F).coeFn_toLp.symm.trans hz
  · intro h
    apply Lp.eq_zero_iff_ae_eq_zero.mpr
    exact (FockAnalyticRestriction.memLp_evaluate lam alpha hlam ha F).coeFn_toLp.trans h

/-- Injectivity of C† is equivalent to the precise analytic uniqueness
property needed: an ℓ² Fock reconstruction vanishing νλ-a.e. on the
imaginary-axis interval must have all coefficients zero. -/
theorem C_adjoint_injective_iff_analytic_uniqueness_ae
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C_adjoint lam alpha hlam ha) ↔
      ∀ F : InfiniteAnalysis.FockCoefficients,
        FockAnalyticRestriction.evaluate alpha ha F =ᵐ[Ultraspherical.measure lam]
          (0 : ℝ → ℂ) → F = 0 := by
  constructor
  · intro hinj F hz
    have hzero :=
      (C_adjoint_eq_zero_iff_analytic_restriction_ae_zero
        lam alpha hlam ha F).mpr hz
    apply hinj
    simpa using hzero
  · intro h F G heq
    have hzero : C_adjoint lam alpha hlam ha (F - G) = 0 := by
      rw [map_sub, heq, sub_self]
    have hfg : F - G = 0 :=
      h (F - G)
        ((C_adjoint_eq_zero_iff_analytic_restriction_ae_zero
          lam alpha hlam ha (F - G)).mp hzero)
    exact sub_eq_zero.mp hfg

/-- Dense range of the genuine Gegenbauer–Fock operator is equivalent
to analytic uniqueness for its actual coherent reconstruction. -/
theorem C_dense_range_iff_analytic_uniqueness_ae
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) ↔
      ∀ F : InfiniteAnalysis.FockCoefficients,
        FockAnalyticRestriction.evaluate alpha ha F =ᵐ[Ultraspherical.measure lam]
          (0 : ℝ → ℂ) → F = 0 := by
  exact (C_dense_range_iff_C_adjoint_injective lam alpha hlam ha).trans
    (C_adjoint_injective_iff_analytic_uniqueness_ae lam alpha hlam ha)

/-- Once analytic uniqueness is established, output-side nonzero Gram
eigenspaces are complete; the required analytic hypothesis remains
visible and is not silently assumed. -/
theorem outputGram_nonzero_eigenspaces_complete_of_analytic_uniqueness_ae
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hunique : ∀ F : InfiniteAnalysis.FockCoefficients,
      FockAnalyticRestriction.evaluate alpha ha F =ᵐ[Ultraspherical.measure lam]
        (0 : ℝ → ℂ) → F = 0) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)
      else
        Module.End.eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  apply outputGram_nonzero_eigenspaces_complete_of_C_adjoint_injective
    lam alpha hlam ha
  exact (C_adjoint_injective_iff_analytic_uniqueness_ae
    lam alpha hlam ha).mpr hunique

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_eq_zero_iff_analytic_restriction_ae_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_injective_iff_analytic_uniqueness_ae
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_dense_range_iff_analytic_uniqueness_ae
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_eigenspaces_complete_of_analytic_uniqueness_ae

end GegenbauerFock.GeneralUltrasphericalFock
