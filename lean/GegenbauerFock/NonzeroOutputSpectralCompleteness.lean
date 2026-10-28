import GegenbauerFock.OutputGramZeroModes
import GegenbauerFock.OutputGramSpectrum

/-!
# V007 — output-side dense range and nonzero spectral completeness bridges

These results concern the actual Gegenbauer--Fock map C : L²(ν_λ) → ℓ²
and the genuine adjoint C†, not finite truncations. They identify
injectivity of C† as the precise remaining analytic-uniqueness obligation
for dense range and for removal of the zero output Gram eigenspace.

The hypotheses are explicit. In particular this module does NOT claim
that C† is unconditionally injective.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Dense range of the actual C is equivalent to injectivity of its
Hilbert adjoint. The proof uses orthogonal-complement duality in
complete Hilbert spaces, with no closed-range assumption. -/
theorem C_dense_range_iff_C_adjoint_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) ↔
      Function.Injective (C_adjoint lam alpha hlam ha) := by
  constructor
  · intro hdense
    have hdouble :
        (C lam alpha hlam ha).rangeᗮᗮ =
          (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
      rw [(C lam alpha hlam ha).range.orthogonal_orthogonal_eq_closure]
      exact hdense
    have horth :
        (C lam alpha hlam ha).rangeᗮ =
          (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
      Submodule.orthogonal_eq_top_iff.mp hdouble
    apply LinearMap.ker_eq_bot.mp
    rw [← (C lam alpha hlam ha).orthogonal_range]
    exact horth
  · intro hinj
    have hker :
        (C_adjoint lam alpha hlam ha).ker =
          (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
      LinearMap.ker_eq_bot.mpr hinj
    have horth :
        (C lam alpha hlam ha).rangeᗮ =
          (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
      rw [(C lam alpha hlam ha).orthogonal_range]
      exact hker
    calc
      (C lam alpha hlam ha).range.topologicalClosure =
          (C lam alpha hlam ha).rangeᗮᗮ :=
        (C lam alpha hlam ha).range.orthogonal_orthogonal_eq_closure.symm
      _ = ⊤ := by rw [horth, Submodule.bot_orthogonal_eq_top]

/-- Zero output Gram modes vanish exactly when the actual operator C
has dense range in the full coefficient Hilbert space. -/
theorem C_dense_range_iff_outputGram_zero_eigenspace_bot
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C lam alpha hlam ha).range.topologicalClosure =
        (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) ↔
      eigenspace (outputGram lam alpha hlam ha).toLinearMap (0 : ℂ) =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  rw [outputGram_zero_eigenspace_eq_C_adjoint_ker, LinearMap.ker_eq_bot]
  exact C_dense_range_iff_C_adjoint_injective lam alpha hlam ha

/-- Under explicitly stated injectivity of C†, the zero output Gram
eigenspace is trivial. No analytic uniqueness theorem is presumed. -/
theorem outputGram_zero_eigenspace_bot_of_C_adjoint_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hinj : Function.Injective (C_adjoint lam alpha hlam ha)) :
    eigenspace (outputGram lam alpha hlam ha).toLinearMap (0 : ℂ) =
      (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  rw [outputGram_zero_eigenspace_eq_C_adjoint_ker]
  exact LinearMap.ker_eq_bot.mpr hinj

/-- The nonzero eigenspaces of CC† are complete in the actual output
Hilbert space, provided C† is injective. This discharges the
operator-theoretic part; analytic uniqueness remains separate. -/
theorem outputGram_nonzero_eigenspaces_complete_of_C_adjoint_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (hinj : Function.Injective (C_adjoint lam alpha hlam ha)) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)
      else
        eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  have hzero :=
    outputGram_zero_eigenspace_bot_of_C_adjoint_injective
      lam alpha hlam ha hinj
  have hsum :
      (⨆ mu : ℂ,
        if mu = 0 then
          (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)
        else
          eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) =
      (⨆ mu : ℂ,
        eigenspace (outputGram lam alpha hlam ha).toLinearMap mu) := by
    apply iSup_congr
    intro mu
    by_cases hmu : mu = 0
    · subst mu
      simp only [ite_true]
      exact hzero.symm
    · simp only [hmu, ite_false]
  rw [hsum]
  exact outputGram_eigenspaces_complete lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_dense_range_iff_C_adjoint_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_dense_range_iff_outputGram_zero_eigenspace_bot
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_eigenspace_bot_of_C_adjoint_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_eigenspaces_complete_of_C_adjoint_injective

end GegenbauerFock.GeneralUltrasphericalFock
