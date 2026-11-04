import Mathlib

/-!
# Manuscript 14.1, Theorem 4 (Sonine) — rational formal-series certificate

This module certifies the second-order radial intertwining identity on
*all formal even coefficient sequences* over Q, and on Mathlib
`PowerSeries ℚ`. The variable of the PowerSeries is u = t².

The moment `moment n` is defined by the exact Sonine recurrence
c₀=1, (2n+3)c_(n+1)=(2n+2)c_n. The analytic identification
c_n=(1/2)∫_{-1}¹ (1-v²)^n dv, continuity of the integral operator on
even entire functions, and the global Bessel identities are NOT
claimed to be kernel-checked here.

All statements in this file use the original pinned Mathlib, without
additional axioms, `sorry`, `sorryAx`, or `Lean.ofReduceBool`.
-/

namespace Manuscript14Sonine

/-- Rational moments for the even Sonine transform. -/
def moment : ℕ → ℚ
  | 0 => 1
  | n + 1 => ((2 * (n : ℚ) + 2) / (2 * (n : ℚ) + 3)) * moment n

theorem moment_zero : moment 0 = 1 := rfl

theorem moment_step (n : ℕ) :
    moment (n + 1) =
      ((2 * (n : ℚ) + 2) / (2 * (n : ℚ) + 3)) * moment n := rfl

theorem moment_pos (n : ℕ) : 0 < moment n := by
  induction n with
  | zero => norm_num [moment]
  | succ n ih =>
      rw [moment_step]
      exact mul_pos (div_pos (by positivity) (by positivity)) ih

/-- The exact recurrence displayed as (2n+3)c_(n+1)=2(n+1)c_n. -/
theorem moment_recurrence (n : ℕ) :
    (2 * (n : ℚ) + 3) * moment (n + 1) =
      (2 * (n : ℚ) + 2) * moment n := by
  rw [moment_step]
  have hd : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
  field_simp [hd] <;> ring

/-- Formal Sonine transform on coefficients f(t)=Σ a_n t^(2n). -/
def sonineCoeff (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  moment n * a n

/-- H₂ f = f''+f'/t, as a formal even Taylor coefficient operator. -/
def radial2Coeff (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (2 * ((n : ℚ) + 1)) ^ 2 * a (n + 1)

/-- H₃ f = f''+2f'/t, as a formal even Taylor coefficient operator. -/
def radial3Coeff (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  (2 * ((n : ℚ) + 1)) * (2 * ((n : ℚ) + 1) + 1) * a (n + 1)

/-- H₃ M = M H₂, for every rational formal even Taylor coefficient sequence. -/
theorem radial_intertwining_coeff (a : ℕ → ℚ) :
    radial3Coeff (sonineCoeff a) = sonineCoeff (radial2Coeff a) := by
  funext n
  dsimp [radial3Coeff, radial2Coeff, sonineCoeff]
  calc
    (2 * ((n : ℚ) + 1)) * (2 * ((n : ℚ) + 1) + 1) *
        (moment (n + 1) * a (n + 1)) =
      (2 * ((n : ℚ) + 1)) *
        ((2 * (n : ℚ) + 3) * moment (n + 1)) * a (n + 1) := by ring
    _ = (2 * ((n : ℚ) + 1)) *
        ((2 * (n : ℚ) + 2) * moment n) * a (n + 1) := by
          rw [moment_recurrence]
    _ = moment n * ((2 * ((n : ℚ) + 1)) ^ 2 * a (n + 1)) := by ring

/-- The same transform in Mathlib's actual PowerSeries type, u=t². -/
noncomputable def soninePS (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (sonineCoeff (fun n => PowerSeries.coeff n f))

noncomputable def radial2PS (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (radial2Coeff (fun n => PowerSeries.coeff n f))

noncomputable def radial3PS (f : PowerSeries ℚ) : PowerSeries ℚ :=
  PowerSeries.mk (radial3Coeff (fun n => PowerSeries.coeff n f))

/-- Genuine PowerSeries equality; no evaluation at t≠0 is asserted. -/
theorem radial_intertwining_powerSeries (f : PowerSeries ℚ) :
    radial3PS (soninePS f) = soninePS (radial2PS f) := by
  apply PowerSeries.ext
  intro n
  simpa only [radial3PS, radial2PS, soninePS,
    PowerSeries.coeff_mk] using
    congrFun (radial_intertwining_coeff
      (fun k => PowerSeries.coeff k f)) n

#print axioms Manuscript14Sonine.moment_pos
#print axioms Manuscript14Sonine.moment_recurrence
#print axioms Manuscript14Sonine.radial_intertwining_coeff
#print axioms Manuscript14Sonine.radial_intertwining_powerSeries

end Manuscript14Sonine
