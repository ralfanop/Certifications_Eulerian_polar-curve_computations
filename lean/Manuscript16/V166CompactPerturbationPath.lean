import Mathlib

/-! M16.6 §13: compact parametrix defects survive compact perturbations.
This is the algebraic and topological homotopy gate for Fredholm index
stability, not a proof that the index is locally constant. Independent
of the forward Fredholm criterion in PR #455. -/
namespace Manuscript16.V166CompactPerturbationPath

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

def HasCompactParametrix (T : E →L[ℂ] F) : Prop :=
  ∃ S : F →L[ℂ] E,
    IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T) ∧
    IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S)

theorem left_defect_add (T K : E →L[ℂ] F) (S : F →L[ℂ] E) :
    (1 : E →L[ℂ] E) - S.comp (T + K) =
      (1 - S.comp T) - S.comp K := by
  ext x
  change x - S (T x + K x) = x - S (T x) - S (K x)
  rw [map_add]
  abel

theorem right_defect_add (T K : E →L[ℂ] F) (S : F →L[ℂ] E) :
    (1 : F →L[ℂ] F) - (T + K).comp S =
      (1 - T.comp S) - K.comp S := by
  ext y
  change y - (T (S y) + K (S y)) = y - T (S y) - K (S y)
  abel

/-- The very same parametrix works for the perturbed operator. -/
theorem same_parametrix_add_compact (T K : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hK : IsCompactOperator K)
    (hL : IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T))
    (hR : IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S)) :
    IsCompactOperator ((1 : E →L[ℂ] E) - S.comp (T + K)) ∧
      IsCompactOperator ((1 : F →L[ℂ] F) - (T + K).comp S) := by
  constructor
  · rw [left_defect_add]
    exact hL.sub (hK.clm_comp S)
  · rw [right_defect_add]
    exact hR.sub (hK.comp_clm S)

theorem parametrix_add_compact (T K : E →L[ℂ] F)
    (hK : IsCompactOperator K) (hT : HasCompactParametrix T) :
    HasCompactParametrix (T + K) := by
  obtain ⟨S, hL, hR⟩ := hT
  exact ⟨S, same_parametrix_add_compact T K S hK hL hR⟩

theorem parametrix_add_compact_iff (T K : E →L[ℂ] F)
    (hK : IsCompactOperator K) :
    HasCompactParametrix (T + K) ↔ HasCompactParametrix T := by
  constructor
  · intro h
    have hn : IsCompactOperator (-K : E →L[ℂ] F) := by
      exact hK.neg
    have hp := parametrix_add_compact (T + K) (-K) hn h
    simpa using hp
  · exact parametrix_add_compact T K hK

/-- A scalar multiple of a compact operator is compact, by composition. -/
theorem compact_scaled (K : E →L[ℂ] F) (hK : IsCompactOperator K) (t : ℂ) :
    IsCompactOperator (t • K : E →L[ℂ] F) := by
  have h := hK.clm_comp (t • (1 : F →L[ℂ] F))
  have he : (t • (1 : F →L[ℂ] F)).comp K = t • K := by
    ext x
    rfl
  rw [he] at h
  exact h

/-- Every point of the affine compact homotopy admits the original parametrix. -/
theorem compact_homotopy_parametrix (T K : E →L[ℂ] F)
    (hK : IsCompactOperator K) (hT : HasCompactParametrix T) (t : ℂ) :
    HasCompactParametrix (T + t • K) :=
  parametrix_add_compact T (t • K) (compact_scaled K hK t) hT

theorem compact_homotopy_continuous (T K : E →L[ℂ] F) :
    Continuous (fun t : ℂ => T + t • K) :=
  continuous_const.add (continuous_id.smul continuous_const)

end Manuscript16.V166CompactPerturbationPath

#print axioms Manuscript16.V166CompactPerturbationPath.left_defect_add
#print axioms Manuscript16.V166CompactPerturbationPath.right_defect_add
#print axioms Manuscript16.V166CompactPerturbationPath.same_parametrix_add_compact
#print axioms Manuscript16.V166CompactPerturbationPath.parametrix_add_compact
#print axioms Manuscript16.V166CompactPerturbationPath.parametrix_add_compact_iff
#print axioms Manuscript16.V166CompactPerturbationPath.compact_scaled
#print axioms Manuscript16.V166CompactPerturbationPath.compact_homotopy_parametrix
#print axioms Manuscript16.V166CompactPerturbationPath.compact_homotopy_continuous
