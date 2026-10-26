import GegenbauerFock.FockSequenceOperator

/-!
# V007: bounded Gaussian Fock point evaluation in the coefficient Hilbert model

For α>0 and z∈ℂ, the reproducing coordinate vector
  k_{α,z}(n) = sqrt(αⁿ/n!) * conjugate(z)^n
belongs to ℓ²(ℕ;ℂ). The resulting Riesz functional
  F ↦ ⟨k_{α,z}, F⟩
is bounded on the actual infinite-dimensional Hilbert space.

This is the mathematically correct coefficient-space point-evaluation
functional; the independent theorem that its values coincide with a
Gaussian-integrable entire function reconstruction is still pending.
-/

open scoped ENNReal InnerProduct

namespace GegenbauerFock.FockEvaluation

/-- The n-th reproducing vector coefficient at a complex point. -/
noncomputable def kernelCoordinate (alpha : ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  ((Real.sqrt (alpha ^ n / (Nat.factorial n : ℝ))) : ℂ) * (star z) ^ n

/-- The squared absolute value has the exact scalar exponential weight. -/
theorem kernelCoordinate_norm_sq (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) (n : ℕ) :
    ‖kernelCoordinate alpha z n‖ ^ 2 =
      (alpha * ‖z‖ ^ 2) ^ n / (Nat.factorial n : ℝ) := by
  have hp : 0 ≤ alpha ^ n / (Nat.factorial n : ℝ) := by positivity
  unfold kernelCoordinate
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_pow, norm_star]
  rw [mul_pow, Real.sq_sqrt hp]
  have hz : (‖z‖ ^ n) ^ 2 = (‖z‖ ^ 2) ^ n := by
    calc
      (‖z‖ ^ n) ^ 2 = ‖z‖ ^ (n * 2) := by rw [pow_mul]
      _ = ‖z‖ ^ (2 * n) := by rw [mul_comm]
      _ = (‖z‖ ^ 2) ^ n := by rw [pow_mul]
  rw [hz]
  ring

/-- The point-evaluation vector is square-summable for every z∈ℂ. -/
theorem kernelCoordinate_memℓp (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) :
    Memℓp (kernelCoordinate alpha z) 2 := by
  apply memℓp_gen
  have hs : Summable (fun n : ℕ => ‖kernelCoordinate alpha z n‖ ^ 2) := by
    simpa only [kernelCoordinate_norm_sq alpha ha z] using
      Real.summable_pow_div_factorial (alpha * ‖z‖ ^ 2)
  simpa using hs

/-- Actual coherent reproducing vector in the infinite Fock Hilbert model. -/
noncomputable def kernelVector (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    FockSequence.Coefficients :=
  ⟨kernelCoordinate alpha z, kernelCoordinate_memℓp alpha ha z⟩

/-- Bounded complex-linear Fock point evaluation via the Riesz map. -/
noncomputable def evaluation (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    FockSequence.Coefficients →L[ℂ] ℂ :=
  innerSL ℂ (kernelVector alpha ha z)

/-- Exact operator norm of the evaluation functional. -/
theorem evaluation_norm (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖evaluation alpha ha z‖ = ‖kernelVector alpha ha z‖ := by
  exact innerSL_apply_norm ℂ (kernelVector alpha ha z)

#print axioms GegenbauerFock.FockEvaluation.kernelCoordinate_norm_sq
#print axioms GegenbauerFock.FockEvaluation.kernelCoordinate_memℓp
#print axioms GegenbauerFock.FockEvaluation.evaluation_norm

end GegenbauerFock.FockEvaluation
