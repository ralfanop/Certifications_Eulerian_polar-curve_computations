import GegenbauerFock.PositivePolarAmplitude
import GegenbauerFock.ConcreteFockCompact

/-!
# V007 — compactness of the positive polar amplitude

The certified positive polar factor P is a bounded self-adjoint positive
operator on the full infinite-dimensional ultraspherical L² source.
Its compactness follows from P = W⁻¹ C, the certified compactness
of the genuine Gegenbauer–Fock map C, and continuity of W⁻¹.
No bounded inverse or spectral gap is asserted.
-/

noncomputable section

open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual Gegenbauer–Fock transform admits a compact, injective,
self-adjoint positive polar amplitude P on its original infinite source,
with C = W P and P² = C†C everywhere. -/
theorem exists_compact_positive_polar_amplitude
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
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) := by
  classical
  obtain ⟨ι, u, mu, W, P, hp, hsum, hK, hPu, hC, hP2, hinj, hself, hPos⟩ :=
    exists_positive_polar_amplitude_kummer lam alpha hlam ha
  have hPexp (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
      P f = W.symm (C lam alpha hlam ha f) := by
    calc
      P f = W.symm (W (P f)) := (W.symm_apply_apply (P f)).symm
      _ = W.symm (C lam alpha hlam ha f) :=
        congrArg W.symm (hC f).symm
  have hcompactP : IsCompactOperator P := by
    have hcomp : IsCompactOperator
        (W.symm.toLinearIsometry.toContinuousLinearMap ∘
          C lam alpha hlam ha) :=
      (C_compact lam alpha hlam ha).clm_comp
        W.symm.toLinearIsometry.toContinuousLinearMap
    have hfun :
        (W.symm.toLinearIsometry.toContinuousLinearMap ∘
          C lam alpha hlam ha) = (P : _ → _) := by
      funext f
      exact (hPexp f).symm
    exact hfun ▸ hcomp
  exact ⟨W, P, hcompactP, hinj, hself, hPos, hC, hP2⟩

/-- Every injective self-adjoint bounded operator on a complete complex Hilbert
space has dense range: the orthogonal complement of its range is its kernel. -/
theorem selfadjoint_injective_range_topologicalClosure_eq_top
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (P : E →L[ℂ] E)
    (hself : P.adjoint = P) (hinj : Function.Injective P) :
    P.range.topologicalClosure = ⊤ := by
  have hker : P.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have horth := P.orthogonal_ker
  rw [hself, hker] at horth
  simpa using horth.symm

/-- The actual compact positive polar factor is injective with dense range
on the entire ultraspherical source Hilbert space, while remaining compact.
No bounded inverse or spectral gap is asserted. -/
theorem exists_compact_positive_polar_amplitude_dense_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ (W : Lp ℂ 2 (Ultraspherical.measure lam) ≃ₗᵢ[ℂ]
        InfiniteAnalysis.FockCoefficients)
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)),
      IsCompactOperator P ∧
      Function.Injective P ∧
      P.range.topologicalClosure = ⊤ ∧
      P.adjoint = P ∧
      (P : Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsPositive ∧
      (∀ f, C lam alpha hlam ha f = W (P f)) ∧
      (∀ f, gram lam alpha hlam ha f = P (P f)) := by
  obtain ⟨W, P, hcompact, hinj, hself, hpositive, hC, hP2⟩ :=
    exists_compact_positive_polar_amplitude lam alpha hlam ha
  have hdense := selfadjoint_injective_range_topologicalClosure_eq_top
    P hself hinj
  exact ⟨W, P, hcompact, hinj, hdense, hself, hpositive, hC, hP2⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_compact_positive_polar_amplitude
#print axioms GegenbauerFock.GeneralUltrasphericalFock.selfadjoint_injective_range_topologicalClosure_eq_top
#print axioms GegenbauerFock.GeneralUltrasphericalFock.exists_compact_positive_polar_amplitude_dense_range

end GegenbauerFock.GeneralUltrasphericalFock
