import Mathlib.NumberTheory.Transcendental.Lindemann.Basic
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Experimental Hermite–Lindemann dependency for Manuscript 14.10, Theorem 11.1

**EXPERIMENTAL BRANCH ONLY.** The source theorem `transcendental_exp` is
from the unmerged Mathlib PR #28013, SHA 54fbfba6f39455b27daaff60830df6a627de8847.
This file deliberately avoids adding any axiom, `sorry`, or `admit`.
Success would certify the *specific exponential instance* against that
PR's code and its own dependencies, not against pinned Mathlib v4.35.
-/

namespace Manuscript14LindemannExperiment

private noncomputable def a : ℝ := 1 / Real.sqrt 2

private theorem a_nonzero : a ≠ 0 := by
  dsimp [a]
  positivity

private theorem a_sq : a ^ 2 = (1 / 2 : ℝ) := by
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hn : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  dsimp [a]
  field_simp [hn]
  nlinarith [hs]

private theorem a_complex_alg : IsAlgebraic ℤ ((a : ℝ) : ℂ) := by
  have hc : (((a : ℝ) : ℂ)) ^ 2 = (2 : ℂ)⁻¹ := by
    norm_cast
    exact a_sq
  have htwo : IsAlgebraic ℤ (2 : ℂ) :=
    isAlgebraic_natCast (R := ℤ) (A := ℂ) 2
  have hinv : IsAlgebraic ℤ (2 : ℂ)⁻¹ := htwo.inv
  apply IsAlgebraic.of_pow (n := 2) (by norm_num)
  rwa [hc]

/-- The Hermite–Lindemann special instance required by the Eulerian
transcendence/aperiodicity argument, under an experimental PR dependency. -/
theorem exp_one_div_sqrt_two_transcendental :
    ¬ IsAlgebraic ℚ (Real.exp (1 / Real.sqrt 2)) := by
  have htrans : Transcendental ℤ (Complex.exp ((a : ℝ) : ℂ)) :=
    transcendental_exp (by exact_mod_cast a_nonzero) a_complex_alg
  intro hQ
  have hQa : IsAlgebraic ℚ (Real.exp a) := by
    simpa only [a] using hQ
  have hQc : IsAlgebraic ℚ (Complex.exp ((a : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_exp] using
      (hQa.algebraMap (A := ℂ))
  have hZc : IsAlgebraic ℤ (Complex.exp ((a : ℝ) : ℂ)) :=
    hQc.restrictScalars ℤ
  exact htrans hZc

#print axioms Manuscript14LindemannExperiment.exp_one_div_sqrt_two_transcendental

end Manuscript14LindemannExperiment
