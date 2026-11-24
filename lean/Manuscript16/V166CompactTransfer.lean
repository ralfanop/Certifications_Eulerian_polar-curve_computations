import Manuscript16.V165GraphNeumann
import Manuscript16.V165TypedGraphSchur

/-! M16 v16.6 frozen §13 (identical to v16.5; source audit #403).
Actual compact-operator transfer, not a scalar Schatten surrogate.
The reference ambient inverse compactness is a stated hypothesis.
No Atkinson theorem or concrete spectral realization is asserted. -/
namespace Manuscript16.V166CompactTransfer

open Manuscript16.V165GraphNeumann
open Manuscript16.V165GraphSchur

variable {𝕜 P D X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

theorem ambientInverse_trans (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (U : X ≃L[𝕜] X) :
    ambientInverse j (L₀.trans U) =
      (ambientInverse j L₀).comp U.symm.toContinuousLinearMap := by
  ext x
  rfl

theorem ambientInverse_trans_cancel (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (U : X ≃L[𝕜] X) :
    ambientInverse j L₀ =
      (ambientInverse j (L₀.trans U)).comp U.toContinuousLinearMap := by
  rw [ambientInverse_trans]
  apply ContinuousLinearMap.ext
  intro x
  change j (L₀.symm x) = j (L₀.symm (U.symm (U x)))
  rw [U.symm_apply_apply]

/-- Compactness is equivalent in both directions under a bounded
invertible right factor. This is an actual Mathlib compact-operator predicate. -/
theorem ambientInverse_compact_iff (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (U : X ≃L[𝕜] X) :
    IsCompactOperator (ambientInverse j (L₀.trans U)) ↔
      IsCompactOperator (ambientInverse j L₀) := by
  constructor
  · intro h
    rw [ambientInverse_trans_cancel j L₀ U]
    exact h.comp_clm U.toContinuousLinearMap
  · intro h
    rw [ambientInverse_trans]
    exact h.comp_clm U.symm.toContinuousLinearMap

/-- Compactness transfer for the actual Neumann inverse constructed in #401. -/
theorem perturbed_inverse_compact_iff [CompleteSpace X]
    (j : D →L[𝕜] X) (L₀ : D ≃L[𝕜] X)
    (E : X →L[𝕜] X) (hG : ‖ambientInverse j L₀‖ ≤ (2 : ℝ)/3)
    (hE : ‖E‖ < (3 : ℝ)/2) :
    IsCompactOperator (ambientInverse j (perturbedEquiv j L₀ E hG hE)) ↔
      IsCompactOperator (ambientInverse j L₀) := by
  unfold perturbedEquiv
  apply ambientInverse_compact_iff

/-- B and C are genuinely bounded on the ambient spaces, not merely in graph norm. -/
def correction (j : D →L[𝕜] X) (B : X →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) : P →L[𝕜] P :=
  B.comp ((ambientInverse j L).comp C)

theorem correction_compact (j : D →L[𝕜] X) (B : X →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X)
    (h : IsCompactOperator (ambientInverse j L)) :
    IsCompactOperator (correction j B C L) := by
  exact (h.comp_clm C).clm_comp B

theorem correction_norm_le (j : D →L[𝕜] X) (B : X →L[𝕜] P)
    (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    ‖correction j B C L‖ ≤ ‖B‖ * ‖ambientInverse j L‖ * ‖C‖ := by
  unfold correction
  calc
    ‖B.comp ((ambientInverse j L).comp C)‖ ≤
        ‖B‖ * ‖(ambientInverse j L).comp C‖ :=
      ContinuousLinearMap.opNorm_comp_le B _
    _ ≤ ‖B‖ * (‖ambientInverse j L‖ * ‖C‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg B)
    _ = ‖B‖ * ‖ambientInverse j L‖ * ‖C‖ := by rw [mul_assoc]

theorem schur_eq_sub_correction (j : D →L[𝕜] X) (A : P →L[𝕜] P)
    (B : X →L[𝕜] P) (C : P →L[𝕜] X) (L : D ≃L[𝕜] X) :
    schur A (B.comp j) C L = A - correction j B C L := by
  apply ContinuousLinearMap.ext
  intro p
  rfl

/-- Compact direct resonant block iff compact Schur block, assuming compact
ambient inverse. Fredholm impossibility itself is a separate obligation. -/
theorem schur_compact_iff (j : D →L[𝕜] X) (A : P →L[𝕜] P)
    (B : X →L[𝕜] P) (C : P →L[𝕜] X) (L : D ≃L[𝕜] X)
    (h : IsCompactOperator (ambientInverse j L)) :
    IsCompactOperator (schur A (B.comp j) C L) ↔ IsCompactOperator A := by
  rw [schur_eq_sub_correction]
  have hk := correction_compact j B C L h
  constructor
  · intro hf
    have he : IsCompactOperator ((A - correction j B C L) + correction j B C L :
        P →L[𝕜] P) := hf.add hk
    simpa only [sub_add_cancel] using he
  · intro ha
    exact ha.sub hk

#print axioms ambientInverse_trans
#print axioms ambientInverse_trans_cancel
#print axioms ambientInverse_compact_iff
#print axioms perturbed_inverse_compact_iff
#print axioms correction_compact
#print axioms correction_norm_le
#print axioms schur_eq_sub_correction
#print axioms schur_compact_iff
end Manuscript16.V166CompactTransfer
