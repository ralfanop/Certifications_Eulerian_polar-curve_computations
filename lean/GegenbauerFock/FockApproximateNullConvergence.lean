import GegenbauerFock.FockApproximateNullSequence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# V007 — a genuine normalized approximate-null sequence

The previously kernel-certified pointwise existence theorem gives, for
each natural n, a unit source vector with an image smaller than
1/(n+1). We now choose all witnesses simultaneously and prove that
their Fock images converge to zero in norm, while every input has norm
one. No nonzero kernel vector is asserted.
-/

noncomputable section

open MeasureTheory Filter

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Simultaneously select genuine unit L² vectors with quantitative
small Fock images. -/
theorem C_exists_normalized_approximate_null_family
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      ∀ n : ℕ,
        ‖u n‖ = 1 ∧
          ‖C lam alpha hlam ha (u n)‖ < 1 / ((n : ℝ) + 1) := by
  classical
  choose u hunit hsmall using
    (fun n : ℕ => C_unit_approximate_null_vector lam alpha hlam ha n)
  exact ⟨u, fun n => ⟨hunit n, hsmall n⟩⟩

/-- The selected unit source vectors are approximate null vectors:
their images converge to zero in the complete Fock coefficient
Hilbert space, although the source norms remain exactly one. -/
theorem C_exists_normalized_approximate_null_sequence
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ∃ u : ℕ → Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ n : ℕ, ‖u n‖ = 1) ∧
        Filter.Tendsto
          (fun n : ℕ => C lam alpha hlam ha (u n))
          Filter.atTop (𝓝 (0 : InfiniteAnalysis.FockCoefficients)) := by
  obtain ⟨u, h⟩ :=
    C_exists_normalized_approximate_null_family lam alpha hlam ha
  refine ⟨u, (fun n => (h n).1), ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero
    (fun n : ℕ => norm_nonneg (C lam alpha hlam ha (u n)))
    (fun n : ℕ => (h n).2.le)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_exists_normalized_approximate_null_family
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_exists_normalized_approximate_null_sequence

end GegenbauerFock.GeneralUltrasphericalFock
