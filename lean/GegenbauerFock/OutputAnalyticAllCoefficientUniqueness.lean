import GegenbauerFock.OutputComplexAnalyticIdentity
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.OfScalars

/-!
# V007 — uniqueness of all complex Fock coefficients

The genuine infinite coherent evaluation is the analytic sum of its
scalar monomial power series. Uniqueness of a one-variable formal
multilinear series then shows that an identically vanishing evaluation
has every weighted coefficient zero. Positivity of the weights removes
them, giving injectivity of the actual Gegenbauer–Fock adjoint.

These declarations are not considered certified until an exact-SHA
Lean CI build and axiom audit have succeeded.
-/

noncomputable section

open Set Filter
open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockEvaluation

/-- The actual ℓ² coherent evaluation has the explicit monomial
formal multilinear series as its power series at the complex origin. -/
theorem hasFPowerSeriesAt_evaluation
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients) :
    HasFPowerSeriesAt (fun z : ℂ => evaluation alpha ha z F)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ =>
          (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n))
      0 := by
  apply hasFPowerSeriesAt_iff.mpr
  apply Filter.Eventually.of_forall
  intro z
  have hinner : HasSum
      (fun n : ℕ => inner ℂ (kernelCoordinate alpha z n) (F n))
      (evaluation alpha ha z F) := by
    rw [evaluation_eq_tsum_inner]
    exact (lp.summable_inner (kernelVector alpha ha z) F).hasSum
  have hterms :
      (fun n : ℕ =>
        z ^ n • (FormalMultilinearSeries.ofScalars ℂ
          (fun k : ℕ =>
            (Real.sqrt (alpha ^ k / (Nat.factorial k : ℝ)) : ℂ) * F k)).coeff n) =
      (fun n : ℕ => inner ℂ (kernelCoordinate alpha z n) (F n)) := by
    funext n
    rw [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      inner_kernelCoordinate_eq_monomial]
    ring
  rw [hterms]
  exact hinner

/-- If the actual entire Fock reconstruction is identically zero,
every (not merely finitely many) ℓ² coefficient is zero. -/
theorem coefficients_eq_zero_of_evaluation_eq_zero
    (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients)
    (hz : (fun z : ℂ => evaluation alpha ha z F) = 0) :
    F = 0 := by
  have hp :
      HasFPowerSeriesAt (0 : ℂ → ℂ)
        (FormalMultilinearSeries.ofScalars ℂ
          (fun n : ℕ =>
            (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n))
        0 := by
    simpa only [hz] using hasFPowerSeriesAt_evaluation alpha ha F
  have hseries :
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ =>
          (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n)) = 0 :=
    hp.eq_zero
  ext n
  have hterm :
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n : ℕ =>
          (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n)) n = 0 := by
    rw [hseries]
    rfl
  have hc :
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n = 0 :=
    (FormalMultilinearSeries.ofScalars_eq_zero ℂ
      (fun n : ℕ =>
        (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) * F n) n).mp hterm
  have hpos : 0 < alpha ^ n / (Nat.factorial n : ℝ) := by positivity
  have hw :
      (Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hpos))
  exact (mul_eq_zero.mp hc).resolve_left hw

#print axioms GegenbauerFock.FockEvaluation.hasFPowerSeriesAt_evaluation
#print axioms GegenbauerFock.FockEvaluation.coefficients_eq_zero_of_evaluation_eq_zero

end GegenbauerFock.FockEvaluation

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Unconditional injectivity of the genuine Gegenbauer–Fock Hilbert
adjoint: complex analytic identity and all Taylor coefficients. -/
theorem C_adjoint_injective_unconditional
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C_adjoint lam alpha hlam ha) := by
  apply C_adjoint_injective_of_interior_unique lam alpha hlam ha
  intro F hzero
  apply FockEvaluation.coefficients_eq_zero_of_evaluation_eq_zero alpha ha F
  exact FockAnalyticRestriction.complex_evaluation_eq_zero_of_interior_zero
    alpha ha F hzero

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_adjoint_injective_unconditional

end GegenbauerFock.GeneralUltrasphericalFock
