/-
Manuscript 15 — the exact analytic jet mechanism separating the first
convolution from all higher M at the terminal Eulerian zero.

Universal local lemmas only. The specialization to the Eulerian sinc
at t=2π/4π is tracked separately and must establish differentiability
at those points using the genuine nonzero sinc quotient.
-/
import Mathlib

noncomputable section
namespace Manuscript15

/-- A zero of a differentiable function becomes a critical point when
    raised to an integer power M≥2. -/
theorem hasDerivAt_power_zero (g : ℝ → ℝ) (x d : ℝ) (M : ℕ)
    (hM : 2 ≤ M) (hg0 : g x = 0) (hg : HasDerivAt g d x) :
    HasDerivAt (fun t => (g t) ^ M) 0 x := by
  have hp : 0 < M - 1 := by omega
  convert hg.pow M using 1
  simp [hg0, hp]

/-- Terminal first-coordinate derivative is exactly a as soon as the
    spectral factor g(t) has a zero and is raised to M≥2. -/
theorem hasDerivAt_power_reconstruction_X
    (a x d : ℝ) (M : ℕ) (hM : 2 ≤ M)
    (g : ℝ → ℝ) (hg0 : g x = 0) (hg : HasDerivAt g d x) :
    HasDerivAt (fun t => a * t * (1 - (g t) ^ M)) a x := by
  have hpow := hasDerivAt_power_zero g x d M hM hg0 hg
  have hfun := (hasDerivAt_id x).mul
    ((hasDerivAt_const x (1 : ℝ)).sub hpow)
  have hp : 0 < M := by omega
  have hval : (g x) ^ M = 0 := by simp [hg0, hp]
  convert hfun.const_mul a using 1 <;> simp [hval] <;> ring

/-- The squared-power coordinate has zero terminal derivative for
    every positive integer M if g itself vanishes there. -/
theorem hasDerivAt_power_reconstruction_Y
    (a x d : ℝ) (M : ℕ) (hM : 1 ≤ M)
    (g : ℝ → ℝ) (hg0 : g x = 0) (hg : HasDerivAt g d x) :
    HasDerivAt (fun t => a * t ^ 2 / 2 * (g t) ^ (2 * M)) 0 x := by
  have hpow := hasDerivAt_power_zero g x d (2 * M)
    (by omega) hg0 hg
  have hpoly : HasDerivAt (fun t : ℝ => a * t ^ 2 / 2) (a * x) x := by
    convert (((hasDerivAt_id x).pow 2).const_mul a).div_const 2 using 1
    · funext u
      ring
    · ring
  have hfun := hpoly.mul hpow
  have hp : 0 < 2 * M := by omega
  have hval : (g x) ^ (2 * M) = 0 := by simp [hg0, hp]
  convert hfun using 1
  · rfl
  · simp [hval]

#print axioms Manuscript15.hasDerivAt_power_zero
#print axioms Manuscript15.hasDerivAt_power_reconstruction_X
#print axioms Manuscript15.hasDerivAt_power_reconstruction_Y

end Manuscript15
