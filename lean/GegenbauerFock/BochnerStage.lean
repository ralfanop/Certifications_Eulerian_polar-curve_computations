import Mathlib

/-!
# V007: a rigorously defined scalar Bochner integral transform

This stage constructs the actual complex-valued Bochner integral
  ∫ f(u) exp(i z u / 2) dμ(u)
for an arbitrary measure μ. Under explicit integrability hypotheses
it proves linearity and norm domination. At zero frequency and for
probability measures it preserves the constant function.

These theorems are *not* yet a bounded operator L²(ν_λ) → Fock_α:
the continuity and square-integrable coherent-state section estimates
needed to construct that operator are separate outstanding theorems.
-/

open MeasureTheory

namespace GegenbauerFock.BochnerStage

/-- Eulerian Fourier coherent exponential section. -/
noncomputable def kernel (z : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (Complex.I * z * (u : ℂ) / 2)

/-- Actual scalar-valued Bochner integral, not a formal kernel symbol. -/
noncomputable def transform (μ : Measure ℝ) (z : ℂ) (f : ℝ → ℂ) : ℂ :=
  ∫ u, f u * kernel z u ∂μ

/-- Additivity when both section-weighted functions are integrable. -/
theorem transform_add (μ : Measure ℝ) (z : ℂ) (f g : ℝ → ℂ)
    (hf : Integrable (fun u => f u * kernel z u) μ)
    (hg : Integrable (fun u => g u * kernel z u) μ) :
    transform μ z (fun u => f u + g u) =
      transform μ z f + transform μ z g := by
  unfold transform
  have h :
      (fun u => (f u + g u) * kernel z u) =
      (fun u => f u * kernel z u + g u * kernel z u) := by
    funext u
    ring
  rw [h]
  exact integral_add hf hg

/-- Scalar homogeneity for the actual complex Bochner integral. -/
theorem transform_const_mul (μ : Measure ℝ) (z c : ℂ) (f : ℝ → ℂ) :
    transform μ z (fun u => c * f u) = c * transform μ z f := by
  unfold transform
  have h :
      (fun u => (c * f u) * kernel z u) =
      (fun u => c * (f u * kernel z u)) := by
    funext u
    ring
  rw [h]
  exact integral_const_mul c _

/-- The transform of zero vanishes. -/
theorem transform_zero (μ : Measure ℝ) (z : ℂ) :
    transform μ z (fun _ => 0) = 0 := by
  simp [transform]

/-- Probability normalization at zero complex frequency. -/
theorem transform_one_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    transform μ 0 (fun _ => 1) = 1 := by
  unfold transform
  have h :
      (fun u : ℝ => (1 : ℂ) * kernel 0 u) = (fun _ => (1 : ℂ)) := by
    funext u
    simp [kernel]
  rw [h]
  simp

/-- Norm domination for the scalar Bochner transform. -/
theorem norm_transform_le_integral_norm (μ : Measure ℝ) (z : ℂ)
    (f : ℝ → ℂ)
    (hf : Integrable (fun u => f u * kernel z u) μ) :
    ‖transform μ z f‖ ≤ ∫ u, ‖f u * kernel z u‖ ∂μ := by
  unfold transform
  exact norm_integral_le_integral_norm _

#print axioms GegenbauerFock.BochnerStage.transform_add
#print axioms GegenbauerFock.BochnerStage.transform_const_mul
#print axioms GegenbauerFock.BochnerStage.transform_one_zero
#print axioms GegenbauerFock.BochnerStage.norm_transform_le_integral_norm


/-- The original complex Eulerian kernel equals its convergent
entire exponential power series at every complex frequency.
Integrating this equality term by term requires an independent
summable-L¹ domination theorem and is not assumed here. -/
theorem kernel_eq_tsum (z : ℂ) (u : ℝ) :
    kernel z u =
      ∑' n : ℕ, (Complex.I * z * (u : ℂ) / 2) ^ n /
        (Nat.factorial n : ℂ) := by
  unfold kernel
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

#print axioms GegenbauerFock.BochnerStage.kernel_eq_tsum

end GegenbauerFock.BochnerStage
