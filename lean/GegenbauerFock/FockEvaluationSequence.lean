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

/-- Exact Gaussian squared norm of the coherent reproducing vector. -/
theorem kernelVector_norm_sq (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖kernelVector alpha ha z‖ ^ 2 = Real.exp (alpha * ‖z‖ ^ 2) := by
  have hnorm : ‖kernelVector alpha ha z‖ ^ 2 =
      (∑' n : ℕ, ‖(kernelVector alpha ha z) n‖ ^ 2) := by
    simpa using (lp.norm_rpow_eq_tsum
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      (kernelVector alpha ha z))
  rw [hnorm]
  simp_rw [show ∀ n : ℕ, (kernelVector alpha ha z) n =
    kernelCoordinate alpha z n from fun _ => rfl]
  simp_rw [kernelCoordinate_norm_sq alpha ha z]
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

theorem evaluation_norm_sq (alpha : ℝ) (ha : 0 < alpha) (z : ℂ) :
    ‖evaluation alpha ha z‖ ^ 2 = Real.exp (alpha * ‖z‖ ^ 2) := by
  rw [evaluation_norm, kernelVector_norm_sq]

/-- Actual infinite Hilbert-series representation of Fock point evaluation,
with norm convergence supplied by the square-summability of both vectors. -/
theorem evaluation_eq_tsum_inner (alpha : ℝ) (ha : 0 < alpha)
    (z : ℂ) (F : FockSequence.Coefficients) :
    evaluation alpha ha z F =
      ∑' n : ℕ, inner ℂ (kernelCoordinate alpha z n) (F n) := by
  change inner ℂ (kernelVector alpha ha z) F = _
  rw [lp.inner_eq_tsum]
  rfl

#print axioms GegenbauerFock.FockEvaluation.kernelCoordinate_norm_sq
#print axioms GegenbauerFock.FockEvaluation.kernelCoordinate_memℓp
#print axioms GegenbauerFock.FockEvaluation.evaluation_norm
#print axioms GegenbauerFock.FockEvaluation.kernelVector_norm_sq
#print axioms GegenbauerFock.FockEvaluation.evaluation_norm_sq
#print axioms GegenbauerFock.FockEvaluation.evaluation_eq_tsum_inner

/-- Exact normalization of the coefficient-model point evaluation:
at z=0 the evaluation functional simply extracts the zeroth coordinate.
This is the starting point for identifying the full Eulerian integral. -/
theorem evaluation_at_zero (alpha : ℝ) (ha : 0 < alpha)
    (F : FockSequence.Coefficients) :
    evaluation alpha ha 0 F = F 0 := by
  rw [evaluation_eq_tsum_inner]
  rw [tsum_eq_single 0]
  · simp [kernelCoordinate]
  · intro n hn
    cases n with
    | zero => contradiction
    | succ n => simp [kernelCoordinate]

#print axioms GegenbauerFock.FockEvaluation.evaluation_at_zero


end GegenbauerFock.FockEvaluation
