import Mathlib

/-!
# V007: bounded coefficients on an actual infinite-dimensional L² Hilbert space

This file constructs a genuine bounded complex-linear functional
  L²(μ; ℂ) → ℂ
from any L² representer, using the Mathlib Riesz inner-product map.
It also records its exact adjoint (rank-one synthesis).

This does NOT yet construct the full Eulerian Fock transform:
we must still prove that the exponential section belongs to L²(νλ)
for each z, build the entire coefficient sequence, and establish its
global weighted ℓ² norm and Hilbert–Schmidt identity.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.L2Coefficient

variable (μ : Measure ℝ)

/-- A genuine bounded complex-linear functional on L²(μ). -/
noncomputable def functional (k : Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℂ] ℂ :=
  InnerProductSpace.innerSL ℂ k

theorem functional_apply (k f : Lp ℂ 2 μ) :
    functional μ k f = ⟪k, f⟫_ℂ := by
  rfl

theorem functional_norm (k : Lp ℂ 2 μ) :
    ‖functional μ k‖ = ‖k‖ := by
  exact InnerProductSpace.innerSL_apply_norm ℂ k

/-- The adjoint is the genuine synthesis map from ℂ back into L²(μ),
not just a formal equality of symbols. -/
theorem functional_adjoint (k : Lp ℂ 2 μ) :
    (functional μ k).adjoint = InnerProductSpace.toSpanSingleton ℂ k := by
  exact ContinuousLinearMap.adjoint_innerSL_apply k

#print axioms GegenbauerFock.L2Coefficient.functional_apply
#print axioms GegenbauerFock.L2Coefficient.functional_norm
#print axioms GegenbauerFock.L2Coefficient.functional_adjoint

end GegenbauerFock.L2Coefficient
