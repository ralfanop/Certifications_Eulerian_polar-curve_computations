import GegenbauerFock.PhyslibMixedGramTraceNormSharp
import GegenbauerFock.PhyslibTraceClassFiniteNormBound

/-!
# V007 — weighted finite sums of arbitrary nonpositive mixed Grams

For arbitrary finite index sets, complex coefficients cᵢ, and bounded
operators Bᵢ,Dᵢ on the actual ultraspherical source Hilbert space,
the non-self-adjoint sum ∑ᵢ cᵢ Bᵢ†(C†C)Dᵢ is genuinely CFC-trace-class.

Its exact source-compatible S₁ norm is bounded by
  [∑ᵢ ‖cᵢ‖ ‖Bᵢ‖ ‖Dᵢ‖] · {}₁F₁(1/2; λ+1; 1/(4α)).
This simultaneously uses the unrestricted trace-class Banach triangle
inequality and the sharp individual mixed-Gram (S₂·S₂ → S₁) bound.
The coefficient of the latter is 1, independently certified elsewhere.

The module is separate from all previously certified checkpoints.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- True proof-carrying Schatten S₁ sum of arbitrary weighted
off-diagonal Gegenbauer--Fock Grams. The indices and coefficients
need not be ordered, positive, real or commuting. -/
noncomputable def gramMixedFiniteTraceClass
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (B D : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.TraceClass (Lp ℂ 2 (Ultraspherical.measure lam)) :=
  ∑ i ∈ s, c i • gramMixedTraceClass lam alpha hlam ha (B i) (D i)

/-- Finite weighted S₁ Kummer bound for nonpositive, noncommuting
mixed Grams. No S₁ positivity or common Hilbert basis is assumed.
This is a genuine CFC trace norm bound on a proof-carrying S₁ element. -/
theorem gramMixedFinite_traceNorm_le_kummer
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (B D : ι → Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam)) :
    ProbabilisticTheory.TraceClass.traceNorm _
      (gramMixedFiniteTraceClass lam alpha hlam ha s c B D) ≤
      (∑ i ∈ s, ‖c i‖ * (‖B i‖ * ‖D i‖)) *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
  classical
  unfold gramMixedFiniteTraceClass
  calc
    ProbabilisticTheory.TraceClass.traceNorm _
      (∑ i ∈ s, c i •
        gramMixedTraceClass lam alpha hlam ha (B i) (D i)) ≤
      ∑ i ∈ s, ‖c i‖ *
        ProbabilisticTheory.TraceClass.traceNorm _
          (gramMixedTraceClass lam alpha hlam ha (B i) (D i)) :=
      ProbabilisticTheory.TraceClass.traceNorm_finset_smul_sum_le
        s c (fun i => gramMixedTraceClass lam alpha hlam ha (B i) (D i))
    _ ≤ ∑ i ∈ s, ‖c i‖ *
      (‖B i‖ * ‖D i‖ *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha))) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (gramMixed_traceNorm_le_kummer_sharp lam alpha hlam ha (B i) (D i))
        (norm_nonneg (c i))
    _ = (∑ i ∈ s, ‖c i‖ * (‖B i‖ * ‖D i‖)) *
        KummerCoefficients.kummerSeries lam (1 / (4 * alpha)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramMixedFinite_traceNorm_le_kummer

end GegenbauerFock.GeneralUltrasphericalFock
