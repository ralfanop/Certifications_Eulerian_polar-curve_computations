import GegenbauerFock.PhyslibGramConjugationIdeal

/-! # V007: Off-diagonal source Gram algebra
The exact operator identity B†G D = (CB)†(CD) is proved for all bounded
source B,D. This does not yet prove trace-class membership or
the S₂·S₂ → S₁ Hölder inequality. Pinned Lean/Mathlib unchanged. -/

noncomputable section
namespace GegenbauerFock.GeneralUltrasphericalFock
open MeasureTheory

noncomputable def gramMixed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  B.adjoint.comp ((gram lam alpha hlam ha).comp D)

theorem gramMixed_eq_composed_adjoints
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    gramMixed lam alpha hlam ha B D =
      ((C lam alpha hlam ha).comp B).adjoint.comp
        ((C lam alpha hlam ha).comp D) := by
  unfold gramMixed gram HilbertGram.gram
  rw [ContinuousLinearMap.adjoint_comp]
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem gramMixed_inner
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam))
    (x y : Lp ℂ 2 (Ultraspherical.measure lam)) :
    inner ℂ (gramMixed lam alpha hlam ha B D x) y =
      inner ℂ (((C lam alpha hlam ha).comp D) x)
        (((C lam alpha hlam ha).comp B) y) := by
  rw [gramMixed_eq_composed_adjoints]
  exact ((C lam alpha hlam ha).comp B).adjoint_inner_left y
    (((C lam alpha hlam ha).comp D) x)

theorem gramMixed_adjoint
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B D : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    (gramMixed lam alpha hlam ha B D).adjoint =
      gramMixed lam alpha hlam ha D B := by
  rw [gramMixed_eq_composed_adjoints
        lam alpha hlam ha B D,
      gramMixed_eq_composed_adjoints
        lam alpha hlam ha D B]
  simp

theorem gramMixed_self
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (B : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    gramMixed lam alpha hlam ha B B =
      gramAfterRight lam alpha hlam ha B := by
  rw [gramAfterRight_eq_conjugated]
  rfl

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_eq_composed_adjoints
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_inner
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_adjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixed_self
end GegenbauerFock.GeneralUltrasphericalFock
