import Mathlib

/-!
# The double-Borel differential intertwiner over complex coefficients

This is the coefficientwise form of the manuscript's Theorem 3.5
over ℂ[[t]]. The type `ℕ → ℂ` is the complete coefficient
representation of a formal series. Analytic convergence is not
assumed or claimed by this theorem.

  L_A = θ + 1/2 - t(θ+1)
  L_F = θ(θ+1/2) - t
  L_F ∘ B² = θ ∘ B² ∘ L_A

The identical rational-coefficient statement is proved separately
in `FormalBorel.lean`.
-/

namespace EulerianSpecialPoint

noncomputable def doubleBorelComplex (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a n / ((n.factorial : ℂ) ^ 2)

noncomputable def operatorAComplex (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => (1 / 2 : ℂ) * a 0
  | n + 1 => (((n + 1 : ℕ) : ℂ) + 1 / 2) * a (n + 1)
      - ((n + 1 : ℕ) : ℂ) * a n

noncomputable def operatorFComplex (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => ((n + 1 : ℕ) : ℂ)
      * (((n + 1 : ℕ) : ℂ) + 1 / 2) * a (n + 1) - a n

def thetaComplex (a : ℕ → ℂ) (n : ℕ) : ℂ := (n : ℂ) * a n

/-- The exact complex-coefficient form of the manuscript's double-Borel
differential intertwining identity; valid for *every* formal input. -/
theorem doubleBorel_intertwines_complex (a : ℕ → ℂ) :
    operatorFComplex (doubleBorelComplex a) =
      thetaComplex (doubleBorelComplex (operatorAComplex a)) := by
  funext n
  cases n with
  | zero => simp [operatorFComplex, thetaComplex]
  | succ n =>
      simp only [operatorFComplex, doubleBorelComplex, operatorAComplex,
        thetaComplex]
      have hn : (n.factorial : ℂ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.factorial_pos n))
      have hn1 : (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero n)
      rw [Nat.factorial_succ]
      push_cast
      field_simp


/-!
The following realizes the same identity in the actual Mathlib type
`PowerSeries ℂ`, rather than merely its coefficient function type.
By definition these four formal operators act through the
corresponding Taylor coefficients.
-/

noncomputable def doubleBorelPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (doubleBorelComplex (fun n => (PowerSeries.coeff n) f))

noncomputable def operatorAPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (operatorAComplex (fun n => (PowerSeries.coeff n) f))

noncomputable def operatorFPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (operatorFComplex (fun n => (PowerSeries.coeff n) f))

noncomputable def thetaPS (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (thetaComplex (fun n => (PowerSeries.coeff n) f))

/-- The double-Borel intertwining equation as a literal identity of
operators on `PowerSeries ℂ`, at every formal power series. -/
theorem doubleBorel_intertwines_powerSeries (f : PowerSeries ℂ) :
    operatorFPS (doubleBorelPS f) =
      thetaPS (doubleBorelPS (operatorAPS f)) := by
  apply PowerSeries.ext
  intro n
  simpa only [operatorFPS, doubleBorelPS, operatorAPS, thetaPS,
    PowerSeries.coeff_mk] using
      congrFun (doubleBorel_intertwines_complex
        (fun j => (PowerSeries.coeff j) f)) n


/-- The coefficientwise Euler operator θ agrees with `X * d/dX`
using Mathlib's actual formal derivative on complex power series. -/
theorem thetaPS_eq_X_derivative (f : PowerSeries ℂ) :
    thetaPS f = PowerSeries.X * PowerSeries.derivative f := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp only [thetaPS, PowerSeries.coeff_mk, thetaComplex, Nat.cast_zero,
        zero_mul]
      exact (PowerSeries.coeff_zero_X_mul (PowerSeries.derivative f)).symm
  | succ n =>
      simp only [thetaPS, PowerSeries.coeff_mk, thetaComplex,
        PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
      push_cast
      ring


/-- Identify the coefficient operator L_A with
θ + 1/2 - X(θ+1) on the actual formal power-series ring. -/
theorem operatorAPS_eq_standard (f : PowerSeries ℂ) :
    operatorAPS f =
      thetaPS f + PowerSeries.C (1 / 2 : ℂ) * f -
        PowerSeries.X * (thetaPS f + f) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [operatorAPS, operatorAComplex, thetaPS, thetaComplex]
  | succ n =>
      simp only [operatorAPS, PowerSeries.coeff_mk, operatorAComplex,
        PowerSeries.coeff_sub, PowerSeries.coeff_add, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, thetaPS, thetaComplex]
      push_cast
      ring

/-- Identify L_F with θ(θ+1/2)-X in Mathlib's power-series ring. -/
theorem operatorFPS_eq_standard (f : PowerSeries ℂ) :
    operatorFPS f =
      thetaPS (thetaPS f + PowerSeries.C (1 / 2 : ℂ) * f) -
        PowerSeries.X * f := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
      simp [operatorFPS, operatorFComplex, thetaPS, thetaComplex]
  | succ n =>
      simp only [operatorFPS, PowerSeries.coeff_mk, operatorFComplex,
        PowerSeries.coeff_sub, PowerSeries.coeff_add, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_succ_X_mul, thetaPS, thetaComplex]
      push_cast
      ring

/-- The manuscript's literal differential-operator identity on ℂ[[t]],
now expressed using sums, products and the formal Euler differential operator. -/
theorem doubleBorel_intertwines_standard (f : PowerSeries ℂ) :
    (thetaPS (thetaPS (doubleBorelPS f) +
        PowerSeries.C (1 / 2 : ℂ) * doubleBorelPS f) -
      PowerSeries.X * doubleBorelPS f) =
      thetaPS (doubleBorelPS (thetaPS f +
        PowerSeries.C (1 / 2 : ℂ) * f -
          PowerSeries.X * (thetaPS f + f))) := by
  rw [← operatorFPS_eq_standard, ← operatorAPS_eq_standard]
  exact doubleBorel_intertwines_powerSeries f

#print axioms EulerianSpecialPoint.operatorAPS_eq_standard
#print axioms EulerianSpecialPoint.operatorFPS_eq_standard
#print axioms EulerianSpecialPoint.doubleBorel_intertwines_standard

#print axioms EulerianSpecialPoint.thetaPS_eq_X_derivative

#print axioms EulerianSpecialPoint.doubleBorel_intertwines_powerSeries

#print axioms EulerianSpecialPoint.doubleBorel_intertwines_complex

end EulerianSpecialPoint
