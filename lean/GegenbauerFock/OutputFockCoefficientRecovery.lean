import GegenbauerFock.OutputPowerSeriesCoefficientUniqueness
import GegenbauerFock.OutputComplexAnalyticIdentity
import GegenbauerFock.NonzeroOutputSpectralCompleteness

/-!
# V007 — coefficient recovery, adjoint injectivity, and output spectrum

The complex coherent Fock evaluation is an entire power series whose
coefficients are nonzero Gaussian/factorial weights times the true
square-summable Fock coordinates. Absolute summability at z=1 follows
from the genuine Fock coherent-vector Hilbert Cauchy--Schwarz bound.

Together with the already checked analytic identity theorem, the
scalar coefficient uniqueness lemma implies injectivity of the full
Hilbert adjoint, density of the Fock transform range, and completeness
of the positive output singular eigenspaces.

This is a new candidate and must pass the pinned Lean and axiom CI.
-/

noncomputable section

open MeasureTheory Module End
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockEvaluation

/-- Coherent coefficient weights (including the true ℓ² coordinate). -/
noncomputable def powerCoefficient
    (alpha : ℝ) (F : FockSequence.Coefficients) (n : ℕ) : ℂ :=
  (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n

/-- The coefficients of the actual entire coherent evaluation are
absolutely summable at z=1. This is a genuine infinite-series
Hilbert Cauchy--Schwarz bound, not a truncated estimate. -/
theorem powerCoefficient_norm_summable
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients) :
    Summable (fun n : ℕ => ‖powerCoefficient alpha F n‖) := by
  have hs : Summable (fun n : ℕ =>
      ‖kernelCoordinate alpha (1 : ℂ) n‖ * ‖F n‖) := by
    exact lp.summable_mul
      (by rw [Real.holderConjugate_iff]; norm_num)
      (kernelVector alpha ha 1) F
  have heq :
      (fun n : ℕ => ‖powerCoefficient alpha F n‖) =
        (fun n : ℕ => ‖kernelCoordinate alpha (1 : ℂ) n‖ * ‖F n‖) := by
    funext n
    simp [powerCoefficient, kernelCoordinate, norm_mul,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [heq]
  exact hs

/-- Global zero coherent evaluation forces ALL true infinite
Fock coordinates to vanish, using scalar power-series uniqueness. -/
theorem coefficients_eq_zero_of_evaluation_eq_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients)
    (hz : (fun z : ℂ => evaluation alpha ha z F) = 0) :
    F = 0 := by
  have hsum : ∀ z : ℂ,
      (∑' n : ℕ, powerCoefficient alpha F n * z ^ n) = 0 := by
    intro z
    have hv : evaluation alpha ha z F = 0 := by
      simpa using congrFun hz z
    have hseries := (evaluation_eq_tsum_monomial alpha ha z F).symm.trans hv
    simpa only [powerCoefficient] using hseries
  have hcoeff := complex_coefficients_zero_of_tsum_monomial_zero
    (powerCoefficient alpha F)
    (powerCoefficient_norm_summable alpha ha F) hsum
  ext n
  have hzcoeff := hcoeff n
  change (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n = 0 at hzcoeff
  have hweight : (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) ≠ 0 := by
    have hp : 0 < alpha ^ n / (Nat.factorial n : ℝ) := by positivity
    exact_mod_cast (Real.sqrt_pos.mpr hp).ne'
  exact (mul_eq_zero.mp hzcoeff).resolve_left hweight

#print axioms GegenbauerFock.FockEvaluation.powerCoefficient_norm_summable
#print axioms GegenbauerFock.FockEvaluation.coefficients_eq_zero_of_evaluation_eq_zero

end GegenbauerFock.FockEvaluation

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The full true Hilbert adjoint of the Gegenbauer--Fock operator is
unconditionally injective, for all positive ultraspherical/Gaussian
parameters. -/
theorem C_adjoint_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C_adjoint lam alpha hlam ha) := by
  intro F G hFG
  have hzero : C_adjoint lam alpha hlam ha (F - G) = 0 := by
    rw [map_sub, hFG, sub_self]
  have heval := C_adjoint_zero_implies_complex_evaluation_zero
    lam alpha hlam ha (F - G) hzero
  exact sub_eq_zero.mp
    (FockEvaluation.coefficients_eq_zero_of_evaluation_eq_zero
      alpha ha (F - G) heval)

/-- The actual ultraspherical Fock analysis operator has dense
range in its entire coefficient Hilbert space. -/
theorem C_range_dense
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C lam alpha hlam ha).range.topologicalClosure =
      (⊤ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  exact (C_dense_range_iff_C_adjoint_injective lam alpha hlam ha).mpr
    (C_adjoint_injective lam alpha hlam ha)

/-- All NONZERO output Gram eigenspaces are complete in the full
coefficient Hilbert space, without a dense-range hypothesis. -/
theorem outputGram_nonzero_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
      if mu = 0 then
        (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients)
      else
        eigenspace (outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ InfiniteAnalysis.FockCoefficients) := by
  exact outputGram_nonzero_eigenspaces_complete_of_C_adjoint_injective
    lam alpha hlam ha (C_adjoint_injective lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_range_dense
#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_nonzero_eigenspaces_complete

end GegenbauerFock.GeneralUltrasphericalFock
