import GegenbauerFock.OutputComplexAnalyticIdentity
import GegenbauerFock.NonzeroOutputSpectralCompleteness
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars

/-!
# V007 — exact coefficient uniqueness and dense range of the Fock transform

The genuine nontruncated coherent reconstruction
  z ↦ ∑' n, sqrt(αⁿ/n!) * zⁿ * F n
is an entire function. A zero entire function has zero formal Taylor
coefficients, by Mathlib's one-dimensional analytic uniqueness theorem.
Every positive Gaussian/factorial coefficient is nonzero, so F=0.

Combined with the separately formalized analytic-identity bridge
C†F=0 → coherent-reconstruction(F)=0, this eliminates ker C† and
proves dense range of the ACTUAL Gegenbauer--Fock transform C.

No finite-rank surrogates, arbitrary injectivity assumptions,
sorry, or new axioms.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.FockEvaluation

/-- Uniqueness of scalar complex power-series coefficients from
a globally vanishing sum, with an explicit summability hypothesis.
The proof uses actual analytic power-series uniqueness at z=0. -/
theorem scalar_power_series_coeff_zero_of_sum_zero
    (a : ℕ → ℂ)
    (hs : ∀ z : ℂ, Summable (fun n : ℕ => a n * z ^ n))
    (hz : ∀ z : ℂ, (∑' n : ℕ, a n * z ^ n) = 0) :
    ∀ n : ℕ, a n = 0 := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ a
  have hseries :
      HasFPowerSeriesAt (fun z : ℂ => ∑' n : ℕ, a n * z ^ n) p 0 := by
    rw [hasFPowerSeriesAt_iff]
    apply Filter.Eventually.of_forall
    intro z
    have h := (hs z).hasSum
    simpa only [p, FormalMultilinearSeries.coeff_ofScalars, zero_add,
      smul_eq_mul, mul_comm] using h
  have hfunc : (fun z : ℂ => ∑' n : ℕ, a n * z ^ n) = 0 := by
    funext z
    exact hz z
  have hzeroPS : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := by
    simpa only [hfunc] using hseries
  have hFormal : p = 0 := hzeroPS.eq_zero
  have ha : a = 0 := by
    exact (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℂ) (c := a)).mp hFormal
  intro n
  exact congrFun ha n

/-- All genuine Fock coordinates vanish when the infinite complex
coherent reconstruction vanishes identically. The nonzero weight is
the ACTUAL Gaussian/factorial coefficient sqrt(αⁿ/n!). -/
theorem coefficients_zero_of_entire_evaluation_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients)
    (hz : (fun z : ℂ => evaluation alpha ha z F) = 0) :
    F = 0 := by
  let a : ℕ → ℂ := fun n =>
    (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n
  have hs (z : ℂ) : Summable (fun n : ℕ => a n * z ^ n) := by
    have h := lp.summable_inner (𝕜 := ℂ) (kernelVector alpha ha z) F
    change Summable (fun n : ℕ =>
      inner ℂ (kernelCoordinate alpha z n) (F n)) at h
    simpa [a, inner_kernelCoordinate_eq_monomial,
      mul_assoc, mul_comm, mul_left_comm] using h
  have hsumzero (z : ℂ) : (∑' n : ℕ, a n * z ^ n) = 0 := by
    calc
      (∑' n : ℕ, a n * z ^ n) = evaluation alpha ha z F := by
        rw [evaluation_eq_tsum_monomial]
        apply tsum_congr
        intro n
        dsimp [a]
        ring
      _ = 0 := congrFun hz z
  have hcoeff := scalar_power_series_coeff_zero_of_sum_zero a hs hsumzero
  ext n
  have hw : (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) ≠ 0 := by
    have hpos : 0 < alpha ^ n / (Nat.factorial n : ℝ) := by positivity
    exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
  have hn : (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n = 0 :=
    hcoeff n
  simpa using (mul_eq_zero.mp hn).resolve_left hw

#print axioms GegenbauerFock.FockEvaluation.scalar_power_series_coeff_zero_of_sum_zero
#print axioms GegenbauerFock.FockEvaluation.coefficients_zero_of_entire_evaluation_zero

end GegenbauerFock.FockEvaluation

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The TRUE Hilbert adjoint C† is injective for every λ,α>0.
Its kernel maps by the certified analytic-identity theorem to a
globally zero entire Fock reconstruction; formal Taylor coefficient
uniqueness makes its coefficient vector zero. -/
theorem C_adjoint_injective_unconditional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C_adjoint lam alpha hlam ha) := by
  intro F G hFG
  have hker : C_adjoint lam alpha hlam ha (F - G) = 0 := by
    rw [map_sub, hFG, sub_self]
  have hzero :=
    C_adjoint_zero_implies_complex_evaluation_zero
      lam alpha hlam ha (F - G) hker
  exact sub_eq_zero.mp
    (FockEvaluation.coefficients_zero_of_entire_evaluation_zero
      alpha ha (F - G) hzero)

/-- Dense range in the *entire* infinite ℓ² coefficient Fock space,
without restriction to a finite span and without further hypotheses. -/
theorem C_dense_range_unconditional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C lam alpha hlam ha).range.topologicalClosure =
      (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
  (C_dense_range_iff_C_adjoint_injective lam alpha hlam ha).mpr
    (C_adjoint_injective_unconditional lam alpha hlam ha)

/-- No residual zero-eigenvector sector of the actual output Gram. -/
theorem outputGram_zero_eigenspace_bot_unconditional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Module.End.eigenspace (outputGram lam alpha hlam ha).toLinearMap (0 : ℂ) =
      (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
  outputGram_zero_eigenspace_bot_of_C_adjoint_injective
    lam alpha hlam ha (C_adjoint_injective_unconditional lam alpha hlam ha)

/-- All nonzero CC† eigenspaces are complete on the output Fock side,
with the analytic uniqueness assumption now fully discharged. -/
theorem outputGram_nonzero_eigenspaces_complete_unconditional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)
      else Module.End.eigenspace
        (outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) :=
  outputGram_nonzero_eigenspaces_complete_of_C_adjoint_injective
    lam alpha hlam ha (C_adjoint_injective_unconditional lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_injective_unconditional
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_dense_range_unconditional
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_zero_eigenspace_bot_unconditional
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_eigenspaces_complete_unconditional

end GegenbauerFock.GeneralUltrasphericalFock
