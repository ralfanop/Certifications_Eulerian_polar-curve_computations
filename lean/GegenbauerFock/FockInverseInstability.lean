import GegenbauerFock.CompactFockProperDenseRange
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# V007 — quantitative instability of inversion on the actual Fock image

The compact Gegenbauer--Fock analysis map has dense, proper and
nonclosed range in the complete infinite coefficient Hilbert space.
Because it is injective but its range is not closed, the Banach
closed-range/antilipschitz equivalence implies that it has no
uniform bounded-below inverse estimate, even restricted to its image.

The last two theorems give a genuine quantitative witness for every
candidate inverse stability constant, without assuming any explicit
singular-value enumeration. This does NOT contradict uniqueness of
reconstruction: injectivity holds, but stable inversion does not.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- No finite anti-Lipschitz constant exists for the actual compact
ultraspherical-to-Fock map. -/
theorem C_not_antilipschitz
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ¬ ∃ K : ℝ≥0, AntilipschitzWith K (C lam alpha hlam ha) := by
  intro hK
  have hclosed : IsClosed (Set.range (C lam alpha hlam ha)) :=
    ((C lam alpha hlam ha).isClosed_range_iff_antilipschitz_of_injective
      (C_injective lam alpha hlam ha)).mpr hK
  apply C_range_not_closed lam alpha hlam ha
  change IsClosed ((C lam alpha hlam ha).range :
    Set InfiniteAnalysis.FockCoefficients) at hclosed
  exact hclosed

/-- For every finite inverse-conditioning constant K, some pair of
source vectors violates that Lipschitz inverse estimate. -/
theorem C_arbitrarily_bad_inverse_conditioning
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ f g : Lp ℂ 2 (Ultraspherical.measure lam),
      (K : ℝ) * dist (C lam alpha hlam ha f) (C lam alpha hlam ha g) <
        dist f g := by
  have hnot : ¬ AntilipschitzWith K (C lam alpha hlam ha) := by
    intro hK
    exact C_not_antilipschitz lam alpha hlam ha ⟨K, hK⟩
  rw [antilipschitzWith_iff_le_mul_dist] at hnot
  push_neg at hnot
  exact hnot

/-- For every finite K, there is an actual nonzero source direction
for which multiplying the output norm by K still underestimates the
input norm. In particular, the inverse on Ran(C) is unbounded. -/
theorem C_no_uniform_lower_norm_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (K : ℝ≥0) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      (K : ℝ) * ‖C lam alpha hlam ha f‖ < ‖f‖ := by
  obtain ⟨f, g, hfg⟩ :=
    C_arbitrarily_bad_inverse_conditioning lam alpha hlam ha K
  refine ⟨f - g, ?_⟩
  rw [map_sub]
  simpa only [dist_eq_norm] using hfg

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_not_antilipschitz
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_arbitrarily_bad_inverse_conditioning
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_no_uniform_lower_norm_bound

end GegenbauerFock.GeneralUltrasphericalFock
