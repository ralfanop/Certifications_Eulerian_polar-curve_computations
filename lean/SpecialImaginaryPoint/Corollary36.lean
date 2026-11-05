import SpecialImaginaryPoint.FormalBorelComplex
import SpecialImaginaryPoint.BorelAnalyticConvergence

/-!
# Manuscript 14.1 — Corollary 3.6: corrected formal domains

The type `ℕ → ℂ` encodes coefficients of `ℂ[[t]]`, and even-series
coefficients of `ℂ[[z²]]` with target variable `u=z²`.
Thus the pullback is defined on ALL formal inputs; no unjustified
"even entire inputs" restriction is imposed.

T: aₙ ↦ (-1/16)ⁿ aₙ.
D = z² d²/dz² + 2z d/dz + z²/4:
(D b)₀=0, (D b)ₙ=(2n)(2n+1)bₙ+(1/4)bₙ₋₁ for n≥1.
-/

namespace EulerianSpecialPoint

/-- The corrected T : ℂ[[t]] → ℂ[[z²]]. -/
noncomputable def evenPullbackCoeff (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (-1 / 16 : ℂ) ^ n * a n

/-- D_(1/2) on even-degree Taylor coefficients. -/
noncomputable def evenEulerianDifferentialCoeff (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      (2 * (((n + 1 : ℕ) : ℂ))) *
        (2 * (((n + 1 : ℕ) : ℂ)) + 1) * a (n + 1) +
        (1 / 4 : ℂ) * a n

/-- D T = 4 T L_F for arbitrary complex formal input. -/
theorem evenEulerianDifferential_pullback (a : ℕ → ℂ) :
    evenEulerianDifferentialCoeff (evenPullbackCoeff a) =
      (fun n => (4 : ℂ) * evenPullbackCoeff (operatorFComplex a) n) := by
  funext n
  cases n with
  | zero => simp [evenEulerianDifferentialCoeff, evenPullbackCoeff,
      operatorFComplex]
  | succ n =>
      simp only [evenEulerianDifferentialCoeff, evenPullbackCoeff,
        operatorFComplex, pow_succ]
      push_cast
      ring

/-- D T B² = 4 T θ B² L_A, still on all complex formal series. -/
theorem evenEulerianDifferential_pullback_doubleBorel (a : ℕ → ℂ) :
    evenEulerianDifferentialCoeff (evenPullbackCoeff (doubleBorelComplex a)) =
      (fun n => (4 : ℂ) *
        evenPullbackCoeff (thetaComplex (doubleBorelComplex (operatorAComplex a))) n) := by
  simpa only [doubleBorel_intertwines_complex] using
    evenEulerianDifferential_pullback (doubleBorelComplex a)

/-- Formal pullback in the actual Mathlib `PowerSeries ℂ` type;
the output indeterminate stands for u=z². -/
noncomputable def evenPullbackPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (evenPullbackCoeff (fun n => (PowerSeries.coeff n) f))

/-- Eulerian second-order generator on even formal power series. -/
noncomputable def evenEulerianDPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (evenEulerianDifferentialCoeff
    (fun n => (PowerSeries.coeff n) f))

/-- PowerSeries-typed D T = 4 T L_F. -/
theorem evenEulerianDPS_pullback (f : PowerSeries ℂ) :
    evenEulerianDPS (evenPullbackPS f) =
      PowerSeries.C (4 : ℂ) * evenPullbackPS (operatorFPS f) := by
  apply PowerSeries.ext
  intro n
  simpa only [evenEulerianDPS, evenPullbackPS, operatorFPS,
    PowerSeries.coeff_mk, PowerSeries.coeff_C_mul] using
      congrFun (evenEulerianDifferential_pullback
        (fun k => (PowerSeries.coeff k) f)) n

/-- PowerSeries-typed D T B² = 4 T θ B² L_A. -/
theorem evenEulerianDPS_pullback_doubleBorel (f : PowerSeries ℂ) :
    evenEulerianDPS (evenPullbackPS (doubleBorelPS f)) =
      PowerSeries.C (4 : ℂ) *
        evenPullbackPS (thetaPS (doubleBorelPS (operatorAPS f))) := by
  rw [evenEulerianDPS_pullback, doubleBorel_intertwines_powerSeries]

/-- Eulerian entire-series coefficient recurrence implies L_F F=0. -/
theorem operatorF_eulerianEntireCoeff_zero :
    operatorFComplex eulerianEntireCoeff = (fun _ => 0) := by
  funext n
  cases n with
  | zero => simp [operatorFComplex]
  | succ n =>
      have h := eulerianEntireCoeff_recurrence n
      calc
        operatorFComplex eulerianEntireCoeff (n + 1) =
            ((n : ℂ) + 1) * ((n : ℂ) + 3 / 2) *
              eulerianEntireCoeff (n + 1) - eulerianEntireCoeff n := by
            simp only [operatorFComplex]
            push_cast
            ring
        _ = 0 := sub_eq_zero.mpr h

/-- Coefficientwise D_(1/2) r_E=0 under the exact Borel profile. -/
theorem evenEulerianD_eulerianCoeff_zero :
    evenEulerianDifferentialCoeff
      (evenPullbackCoeff eulerianEntireCoeff) = (fun _ => 0) := by
  rw [evenEulerianDifferential_pullback,
    operatorF_eulerianEntireCoeff_zero]
  funext n
  simp [evenPullbackCoeff]

#print axioms EulerianSpecialPoint.evenEulerianDifferential_pullback
#print axioms EulerianSpecialPoint.evenEulerianDifferential_pullback_doubleBorel
#print axioms EulerianSpecialPoint.evenEulerianDPS_pullback
#print axioms EulerianSpecialPoint.evenEulerianDPS_pullback_doubleBorel
#print axioms EulerianSpecialPoint.operatorF_eulerianEntireCoeff_zero
#print axioms EulerianSpecialPoint.evenEulerianD_eulerianCoeff_zero

end EulerianSpecialPoint
