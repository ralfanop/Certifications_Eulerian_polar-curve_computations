import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Shared Fredholm F8 continuation, applicable to M16.6 §13.
Compact perturbations preserve the left and right compact parametrix defects.
This proves the algebraic/operator-ideal step of Atkinson stability
without assuming any norm bound on the perturbation or normality.
Closed range and finite defects are addressed by #455; index constancy
on the resulting continuous Fredholm path remains a separate obligation. -/
namespace SharedCore.FredholmCompactPerturbation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem left_defect_add_compact
    (T P : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hL : IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T))
    (hP : IsCompactOperator P) :
    IsCompactOperator ((1 : E →L[ℂ] E) - S.comp (T + P)) := by
  have hSP : IsCompactOperator (S.comp P) := hP.clm_comp S
  have he : (1 : E →L[ℂ] E) - S.comp (T + P) =
      ((1 : E →L[ℂ] E) - S.comp T) - S.comp P := by
    ext x
    change x - S (T x + P x) = x - S (T x) - S (P x)
    rw [map_add]
    abel
  rw [he]
  exact hL.sub hSP

theorem right_defect_add_compact
    (T P : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hR : IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S))
    (hP : IsCompactOperator P) :
    IsCompactOperator ((1 : F →L[ℂ] F) - (T + P).comp S) := by
  have hPS : IsCompactOperator (P.comp S) := hP.comp_clm S
  have he : (1 : F →L[ℂ] F) - (T + P).comp S =
      ((1 : F →L[ℂ] F) - T.comp S) - P.comp S := by
    ext x
    change x - (T (S x) + P (S x)) = x - T (S x) - P (S x)
    abel
  rw [he]
  exact hR.sub hPS

/-- The same parametrix works along the entire affine compact-perturbation path. -/
theorem compact_defects_affine_path
    (T P : E →L[ℂ] F) (S : F →L[ℂ] E)
    (hL : IsCompactOperator ((1 : E →L[ℂ] E) - S.comp T))
    (hR : IsCompactOperator ((1 : F →L[ℂ] F) - T.comp S))
    (hP : IsCompactOperator P) (t : ℂ) :
    IsCompactOperator ((1 : E →L[ℂ] E) - S.comp (T + t • P)) ∧
    IsCompactOperator ((1 : F →L[ℂ] F) - (T + t • P).comp S) := by
  have ht : IsCompactOperator (t • P) := hP.smul t
  exact ⟨left_defect_add_compact T (t • P) S hL ht,
    right_defect_add_compact T (t • P) S hR ht⟩

end SharedCore.FredholmCompactPerturbation

#print axioms SharedCore.FredholmCompactPerturbation.left_defect_add_compact
#print axioms SharedCore.FredholmCompactPerturbation.right_defect_add_compact
#print axioms SharedCore.FredholmCompactPerturbation.compact_defects_affine_path
