import Mathlib
import SpecialImaginaryPoint.SonineRadialFormal

/-!
# Manuscript 14.1, §4: complex formal Sonine radial intertwining

Extend the real/rational coefficientwise H3 ∘ M = M ∘ H2 identity
to arbitrary complex coefficient sequences and actual PowerSeries ℂ.
This is a formal-series theorem, not yet an identity of analytic
functions evaluated at complex t.
-/

namespace Manuscript14Sonine

noncomputable def momentComplex (n : ℕ) : ℂ := (moment n : ℂ)

theorem momentComplex_recurrence (n : ℕ) :
    (2 * (n : ℂ) + 3) * momentComplex (n + 1) =
      (2 * (n : ℂ) + 2) * momentComplex n := by
  change (2 * (n : ℂ) + 3) * (moment (n + 1) : ℂ) =
    (2 * (n : ℂ) + 2) * (moment n : ℂ)
  exact_mod_cast moment_recurrence n

noncomputable def sonineCoeffComplex (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  momentComplex n * a n

noncomputable def radial2CoeffComplex (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (2 * ((n : ℂ) + 1)) ^ 2 * a (n + 1)

noncomputable def radial3CoeffComplex (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  (2 * ((n : ℂ) + 1)) * (2 * ((n : ℂ) + 1) + 1) * a (n + 1)

/-- Complex formal radial intertwining, without growth assumptions. -/
theorem radial_intertwining_coeff_complex (a : ℕ → ℂ) :
    radial3CoeffComplex (sonineCoeffComplex a) =
      sonineCoeffComplex (radial2CoeffComplex a) := by
  funext n
  dsimp [radial3CoeffComplex, radial2CoeffComplex, sonineCoeffComplex]
  calc
    (2 * ((n : ℂ) + 1)) * (2 * ((n : ℂ) + 1) + 1) *
        (momentComplex (n + 1) * a (n + 1)) =
      (2 * ((n : ℂ) + 1)) *
        ((2 * (n : ℂ) + 3) * momentComplex (n + 1)) * a (n + 1) := by ring
    _ = (2 * ((n : ℂ) + 1)) *
        ((2 * (n : ℂ) + 2) * momentComplex n) * a (n + 1) := by
          rw [momentComplex_recurrence]
    _ = momentComplex n *
        ((2 * ((n : ℂ) + 1)) ^ 2 * a (n + 1)) := by ring

noncomputable def soninePSComplex (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (sonineCoeffComplex (fun n => PowerSeries.coeff n f))

noncomputable def radial2PSComplex (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (radial2CoeffComplex (fun n => PowerSeries.coeff n f))

noncomputable def radial3PSComplex (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (radial3CoeffComplex (fun n => PowerSeries.coeff n f))

theorem radial_intertwining_powerSeries_complex (f : PowerSeries ℂ) :
    radial3PSComplex (soninePSComplex f) =
      soninePSComplex (radial2PSComplex f) := by
  apply PowerSeries.ext
  intro n
  simpa only [radial3PSComplex, radial2PSComplex, soninePSComplex,
    PowerSeries.coeff_mk] using
    congrFun (radial_intertwining_coeff_complex
      (fun k => PowerSeries.coeff k f)) n

#print axioms Manuscript14Sonine.momentComplex_recurrence
#print axioms Manuscript14Sonine.radial_intertwining_coeff_complex
#print axioms Manuscript14Sonine.radial_intertwining_powerSeries_complex

end Manuscript14Sonine
