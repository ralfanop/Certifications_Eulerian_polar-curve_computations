import GegenbauerFock.CompactPositivePolarAmplitude
import GegenbauerFock.CompactFockProperDenseRange
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# V007 — the genuine positive polar amplitude has dense, proper range

The positive compact polar factor P of the true Gegenbauer--Fock
transform C = W P is injective with dense but non-surjective range.
The density follows from P being self-adjoint and injective;
non-surjectivity transfers from the certified obstruction for C
through the unitary W. No continuous inverse of P is asserted.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual positive polar amplitude is a compact quasiaffinity
on the ultraspherical source: compact, positive, self-adjoint,
injective, with dense proper range. -/
theorem exists_compact_positive_polar_proper_dense_range
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
      ¬ Function.Surjective P ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) := by
  classical
  obtain ⟨W, P, hcompact, hinj, hself, hpositive, hC, hP2⟩ :=
    exists_compact_positive_polar_amplitude lam alpha hlam ha
  have hdense :
      P.range.topologicalClosure =
        (⊤ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
    have hker : P.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
    apply (Submodule.topologicalClosure_eq_top_iff).2
    rw [P.orthogonal_range, hself, hker]
  have hproper : ¬ Function.Surjective P := by
    intro hsurj
    apply C_not_surjective lam alpha hlam ha
    intro F
    obtain ⟨f, hf⟩ := hsurj (W.symm F)
    refine ⟨f, ?_⟩
    calc
      C lam alpha hlam ha f = W (P f) := hC f
      _ = W (W.symm F) := by rw [hf]
      _ = F := W.apply_symm_apply F
  exact ⟨W, P, hcompact, hinj, hself, hpositive,
    hdense, hproper, hC, hP2⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_compact_positive_polar_proper_dense_range

end GegenbauerFock.GeneralUltrasphericalFock
