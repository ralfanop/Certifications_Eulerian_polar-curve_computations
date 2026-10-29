import GegenbauerFock.CompactPositivePolarProperDenseRange

/-!
# V007 — non-closed range of the positive compact polar amplitude

The true polar amplitude P of the Gegenbauer--Fock transform is a
compact injective positive self-adjoint operator with dense proper
range. A dense linear subspace which is closed must be the whole
Hilbert space, so its image is not closed. No bounded inverse of P
or spectral gap at zero is asserted.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual positive polar amplitude of the Gegenbauer--Fock
transform has nonclosed dense proper range on the ultraspherical
source Hilbert space. -/
theorem exists_positive_polar_amplitude_nonclosed_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)),
      IsCompactOperator P ∧
      Function.Injective P ∧
      P.adjoint = P ∧
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsPositive ∧
      P.range.topologicalClosure =
        (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      ¬ IsClosed
        (P.range : Set (Lp ℂ 2 (Ultraspherical.measure lam))) ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) := by
  classical
  obtain ⟨W, P, hcompact, hinj, hself, hpositive, hdense, hproper, hC, hP2⟩ :=
    exists_compact_positive_polar_proper_dense_range lam alpha hlam ha
  have hnotclosed :
      ¬ IsClosed (P.range :
        Set (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    intro hclosed
    have htop : P.range =
        (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
      calc
        P.range = P.range.topologicalClosure :=
          (hclosed.submodule_topologicalClosure_eq).symm
        _ = ⊤ := hdense
    exact hproper (LinearMap.range_eq_top.mp htop)
  exact ⟨W, P, hcompact, hinj, hself, hpositive,
    hdense, hnotclosed, hC, hP2⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_positive_polar_amplitude_nonclosed_range

end GegenbauerFock.GeneralUltrasphericalFock
