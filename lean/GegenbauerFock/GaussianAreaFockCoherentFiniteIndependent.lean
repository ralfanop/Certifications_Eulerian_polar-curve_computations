import GegenbauerFock.GaussianAreaFiniteCoherentVandermonde
import GegenbauerFock.FockEvaluationSequence
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# V007 — linear independence of finite coefficient Fock coherent kernels

A vanishing finite linear combination of coefficient-model Gaussian Fock
kernel vectors gives zero at each ℓ² coordinate. The first n coordinates
are the Vandermonde power moments at the conjugate nodes multiplied by
strictly positive common Gaussian normalization constants. Distinct nodes
therefore force every coefficient to vanish.
-/

noncomputable section

namespace GegenbauerFock.GaussianArea

/-- The actual Gaussian Fock coefficient kernel vectors associated to
pairwise distinct complex nodes are linearly independent. -/
theorem finiteFockCoherentKernel_zero_coefficients
    (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (z c : Fin n → ℂ) (hz : Function.Injective z)
    (hzero : ∑ i : Fin n,
      c i • FockEvaluation.kernelVector alpha ha (z i) = 0) :
    ∀ i : Fin n, c i = 0 := by
  have hcoord (k : ℕ) :
      ∑ i : Fin n, c i * FockEvaluation.kernelCoordinate alpha (z i) k = 0 := by
    have hk := congrArg
      (fun F : FockSequence.Coefficients => F k) hzero
    simpa only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, lp.coeFn_zero,
      Pi.zero_apply, FockEvaluation.kernelVector] using hk
  have hpower (k : Fin n) :
      ∑ i : Fin n, c i * (star (z i)) ^ (k : ℕ) = 0 := by
    have hfactor :
        (∑ i : Fin n,
          c i * (((Real.sqrt
            (alpha ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ))) : ℂ) *
              (star (z i)) ^ (k : ℕ))) =
        ((Real.sqrt
            (alpha ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ))) : ℂ) *
          (∑ i : Fin n, c i * (star (z i)) ^ (k : ℕ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hzeroCoord := hcoord (k : ℕ)
    dsimp [FockEvaluation.kernelCoordinate] at hzeroCoord
    change (∑ i : Fin n,
      c i * (((Real.sqrt
        (alpha ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ))) : ℂ) *
          (star (z i)) ^ (k : ℕ))) = 0 at hzeroCoord
    rw [hfactor] at hzeroCoord
    have hfac : 0 < (Nat.factorial (k : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (k : ℕ)
    have hratio : 0 < alpha ^ (k : ℕ) /
        (Nat.factorial (k : ℕ) : ℝ) :=
      div_pos (pow_pos ha _) hfac
    have hsqrt : ((Real.sqrt
        (alpha ^ (k : ℕ) / (Nat.factorial (k : ℕ) : ℝ))) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hratio))
    exact (mul_eq_zero.mp hzeroCoord).resolve_left hsqrt
  exact finite_conjugate_vandermonde_moments_zero_coefficients
    n z c hz hpower

/-- Finite Gaussian Fock kernel vectors at distinct complex nodes form
a linearly independent family in the genuine complex Hilbert coefficient
space. -/
theorem finiteFockCoherentKernel_linearIndependent
    (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (z : Fin n → ℂ) (hz : Function.Injective z) :
    LinearIndependent ℂ (fun i : Fin n =>
      FockEvaluation.kernelVector alpha ha (z i)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  exact finiteFockCoherentKernel_zero_coefficients n alpha ha z c hz hc i

#print axioms GegenbauerFock.GaussianArea.finiteFockCoherentKernel_linearIndependent

#print axioms GegenbauerFock.GaussianArea.finiteFockCoherentKernel_zero_coefficients

end GegenbauerFock.GaussianArea
