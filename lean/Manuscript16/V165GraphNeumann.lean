import Mathlib

/-! M16 v16.5 §13, mixed-Linverse-164 and mixed-inverse-bound-164.
Actual Banach-space Neumann inversion on distinct graph and ambient spaces.
The reference graph equivalence and inverse ambient norm are explicit inputs;
the concrete spectral realization and Schatten assertions remain separate. -/
namespace Manuscript16.V165GraphNeumann

variable {𝕜 D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

/-- The inverse on the ambient space, not the inverse in graph norm. -/
def ambientInverse (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X) : X →L[𝕜] X :=
  j.comp L₀.symm.toContinuousLinearMap

/-- Actual endomorphism equivalence from the convergent geometric series. -/
noncomputable def onePlusEquiv (Q : X →L[𝕜] X) (hQ : ‖Q‖ < 1) : X ≃L[𝕜] X :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (-Q) (by simpa using hQ))

theorem onePlusEquiv_apply (Q : X →L[𝕜] X) (hQ : ‖Q‖ < 1) (x : X) :
    onePlusEquiv Q hQ x = x + Q x := by
  change ((↑(Units.oneSub (-Q) (by simpa using hQ)) : X →L[𝕜] X) x) = _
  rw [Units.val_oneSub]
  simp

theorem perturbation_norm_lt_one (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (E : X →L[𝕜] X) (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3)
    (hE : ‖E‖ < (3 : ℝ)/2) :
    ‖E.comp (ambientInverse j L₀)‖ < 1 := by
  calc
    ‖E.comp (ambientInverse j L₀)‖ ≤ ‖E‖ * ‖ambientInverse j L₀‖ :=
      ContinuousLinearMap.opNorm_comp_le E (ambientInverse j L₀)
    _ ≤ ‖E‖ * ((2 : ℝ)/3) := mul_le_mul_of_nonneg_left hG (norm_nonneg E)
    _ < 1 := by linarith

/-- Invertible perturbed map on the same domain D. -/
noncomputable def perturbedEquiv (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (E : X →L[𝕜] X) (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3)
    (hE : ‖E‖ < (3 : ℝ)/2) : D ≃L[𝕜] X :=
  L₀.trans (onePlusEquiv (E.comp (ambientInverse j L₀))
    (perturbation_norm_lt_one j L₀ E hG hE))

theorem perturbedEquiv_apply (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (E : X →L[𝕜] X) (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3)
    (hE : ‖E‖ < (3 : ℝ)/2) (d : D) :
    perturbedEquiv j L₀ E hG hE d = L₀ d + E (j d) := by
  change onePlusEquiv (E.comp (ambientInverse j L₀))
    (perturbation_norm_lt_one j L₀ E hG hE) (L₀ d) = _
  rw [onePlusEquiv_apply]
  simp [ambientInverse]

theorem perturbed_inverse_formula (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (E : X →L[𝕜] X) (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3)
    (hE : ‖E‖ < (3 : ℝ)/2) (x : X) :
    (perturbedEquiv j L₀ E hG hE).symm x =
      L₀.symm ((onePlusEquiv (E.comp (ambientInverse j L₀))
        (perturbation_norm_lt_one j L₀ E hG hE)).symm x) := by
  rfl

/-- Sharp ambient inverse bound, not a graph-norm bound. -/
theorem perturbed_inverse_norm (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (E : X →L[𝕜] X) (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3)
    (hE : ‖E‖ < (3 : ℝ)/2) :
    ‖ambientInverse j (perturbedEquiv j L₀ E hG hE)‖ ≤
      1 / ((3 : ℝ)/2 - ‖E‖) := by
  have hpos : 0 < (3 : ℝ)/2 - ‖E‖ := by linarith
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let d := (perturbedEquiv j L₀ E hG hE).symm x
  change ‖j d‖ ≤ (1 / ((3 : ℝ)/2 - ‖E‖)) * ‖x‖
  have hx : L₀ d + E (j d) = x := by
    rw [← perturbedEquiv_apply j L₀ E hG hE d]
    exact (perturbedEquiv j L₀ E hG hE).apply_symm_apply x
  have h0 : ‖j d‖ ≤ ((2 : ℝ)/3) * ‖L₀ d‖ := by
    calc
      ‖j d‖ = ‖ambientInverse j L₀ (L₀ d)‖ := by simp [ambientInverse]
      _ ≤ ‖ambientInverse j L₀‖ * ‖L₀ d‖ := (ambientInverse j L₀).le_opNorm _
      _ ≤ ((2 : ℝ)/3) * ‖L₀ d‖ := mul_le_mul_of_nonneg_right hG (norm_nonneg _)
  have h1 : ‖L₀ d‖ ≤ ‖x‖ + ‖E‖ * ‖j d‖ := by
    calc
      ‖L₀ d‖ = ‖x - E (j d)‖ := by rw [← hx, add_sub_cancel_right]
      _ ≤ ‖x‖ + ‖E (j d)‖ := norm_sub_le _ _
      _ ≤ ‖x‖ + ‖E‖ * ‖j d‖ := add_le_add_right (E.le_opNorm (j d)) ‖x‖
  have hb : ‖j d‖ * ((3 : ℝ)/2 - ‖E‖) ≤ ‖x‖ := by nlinarith
  rw [one_div, inv_mul_eq_div]
  exact (le_div_iff₀ hpos).2 hb

#print axioms onePlusEquiv_apply
#print axioms perturbation_norm_lt_one
#print axioms perturbedEquiv_apply
#print axioms perturbed_inverse_formula
#print axioms perturbed_inverse_norm
end Manuscript16.V165GraphNeumann
