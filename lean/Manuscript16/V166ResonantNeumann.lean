import Mathlib
import Manuscript16.V165SchurClosedRange

/-! M16.6 §13: mixed-gap-164, mixed-neumann-164.
The resonant Schur map is an actual bounded operator on P. The ambient
inverse estimate for the graph-domain equivalence L is an explicit input
(cf. the checked V165GraphNeumann.perturbed_inverse_norm).
No concrete Maxwell–Dirac realization or general det4 claim. -/
namespace Manuscript16.V166ResonantNeumann

open Manuscript16.V165GraphSchur

variable {𝕜 P D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P] [CompleteSpace P]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]

def coupling (B : X →L[𝕜] P) (G : X →L[𝕜] X) (C : P →L[𝕜] X) :
    P →L[𝕜] P := B.comp (G.comp C)

def scalarSchur (μ : 𝕜) (K : P →L[𝕜] P) : P →L[𝕜] P :=
  μ • ContinuousLinearMap.id 𝕜 P - K

theorem coupling_norm (B : X →L[𝕜] P) (G : X →L[𝕜] X) (C : P →L[𝕜] X) :
    ‖coupling B G C‖ ≤ ‖B‖ * (‖G‖ * ‖C‖) := by
  calc
    _ ≤ ‖B‖ * ‖G.comp C‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le G C)
      (norm_nonneg B)

theorem coupling_gap_bound (B : X →L[𝕜] P) (G : X →L[𝕜] X)
    (C : P →L[𝕜] X) (E : X →L[𝕜] X)
    (hG : ‖G‖ ≤ 1 / ((3 : ℝ)/2 - ‖E‖)) :
    ‖coupling B G C‖ ≤ ‖B‖ * ‖C‖ / ((3 : ℝ)/2 - ‖E‖) := by
  calc
    _ ≤ ‖B‖ * (‖G‖ * ‖C‖) := coupling_norm B G C
    _ ≤ ‖B‖ * ((1 / ((3 : ℝ)/2 - ‖E‖)) * ‖C‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hG (norm_nonneg C))
        (norm_nonneg B)
    _ = _ := by simp only [div_eq_mul_inv, one_mul]; ring

theorem normalized_norm_lt_one (μ : 𝕜) (K : P →L[𝕜] P) (h : ‖K‖ < ‖μ‖) :
    ‖μ⁻¹ • K‖ < 1 := by
  have hp : 0 < ‖μ‖ := lt_of_le_of_lt (norm_nonneg K) h
  rw [norm_smul, norm_inv, inv_mul_eq_div]
  exact (div_lt_one hp).2 h

theorem scalarSchur_bijective (μ : 𝕜) (K : P →L[𝕜] P) (h : ‖K‖ < ‖μ‖) :
    Function.Bijective (scalarSchur μ K) := by
  have hμ : μ ≠ 0 := norm_pos_iff.mp (lt_of_le_of_lt (norm_nonneg K) h)
  let Q : P →L[𝕜] P := μ⁻¹ • K
  have hQ : ‖Q‖ < 1 := normalized_norm_lt_one μ K h
  let U : P ≃L[𝕜] P := ContinuousLinearEquiv.ofUnit (Units.oneSub Q hQ)
  have hU (x : P) : U x = x - Q x := by
    change ((↑(Units.oneSub Q hQ) : P →L[𝕜] P) x) = _
    rw [Units.val_oneSub]
    simp
  have hf (x : P) : scalarSchur μ K x = μ • U x := by
    change μ • x - K x = μ • U x
    rw [hU, smul_sub]
    dsimp [Q]
    rw [smul_smul, mul_inv_cancel₀ hμ, one_smul]
  constructor
  · intro x y hxy
    apply U.injective
    have hh := congrArg (fun z : P => μ⁻¹ • z) hxy
    change μ⁻¹ • (scalarSchur μ K x) = μ⁻¹ • (scalarSchur μ K y) at hh
    rw [hf x, hf y, smul_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul, one_smul] at hh
    exact hh
  · intro y
    refine ⟨U.symm (μ⁻¹ • y), ?_⟩
    rw [hf, U.apply_symm_apply, smul_smul, mul_inv_cancel₀ hμ, one_smul]

theorem scalarSchur_coercive (μ : 𝕜) (K : P →L[𝕜] P) (h : ‖K‖ < ‖μ‖) (x : P) :
    ‖x‖ ≤ ‖scalarSchur μ K x‖ / (‖μ‖ - ‖K‖) := by
  have hp : 0 < ‖μ‖ - ‖K‖ := sub_pos.mpr h
  have he : μ • x = scalarSchur μ K x + K x := by
    change μ • x = μ • x - K x + K x
    abel
  have hb : ‖μ‖ * ‖x‖ ≤ ‖scalarSchur μ K x‖ + ‖K‖ * ‖x‖ := by
    calc
      _ = ‖μ • x‖ := (norm_smul μ x).symm
      _ = ‖scalarSchur μ K x + K x‖ := congrArg norm he
      _ ≤ ‖scalarSchur μ K x‖ + ‖K x‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_left (K.le_opNorm x) _
  apply (le_div_iff₀ hp).2
  nlinarith

theorem resonant_block_bijective (μ : 𝕜) (j : D →L[𝕜] X) (L : D ≃L[𝕜] X)
    (B : X →L[𝕜] P) (C : P →L[𝕜] X) (E : X →L[𝕜] X)
    (hE : ‖E‖ < (3 : ℝ)/2)
    (hG : ‖j.comp L.symm.toContinuousLinearMap‖ ≤ 1 / ((3 : ℝ)/2 - ‖E‖))
    (hgap : ‖B‖ * ‖C‖ / ((3 : ℝ)/2 - ‖E‖) < ‖μ‖) :
    Function.Bijective (block (μ • ContinuousLinearMap.id 𝕜 P) (B.comp j) C L) := by
  let K := coupling B (j.comp L.symm.toContinuousLinearMap) C
  have hK : ‖K‖ < ‖μ‖ :=
    lt_of_le_of_lt (coupling_gap_bound B _ C E hG) hgap
  have he : schur (μ • ContinuousLinearMap.id 𝕜 P) (B.comp j) C L =
      scalarSchur μ K := by
    ext x
    rfl
  apply (block_bijective_iff _ _ _ _).2
  rw [he]
  exact scalarSchur_bijective μ K hK

#print axioms coupling_norm
#print axioms coupling_gap_bound
#print axioms normalized_norm_lt_one
#print axioms scalarSchur_bijective
#print axioms scalarSchur_coercive
#print axioms resonant_block_bijective

end Manuscript16.V166ResonantNeumann
