import Mathlib

/-!
# V007: bounded and compact finite coefficient truncations on genuine L²

Given finitely many actual L² representers, combine their bounded Riesz
coefficient functionals into a continuous linear map from L²(μ;ℂ)
to ℂ^N (finite product norm). This map is compact because its
codomain is finite-dimensional.

This is a *truncation layer*; it does not yet establish norm convergence
of those maps in the Bargmann–Fock Hilbert space and must not be
confused with compactness of the complete Gegenbauer–Fock transform.
-/

open MeasureTheory

namespace GegenbauerFock.FiniteCoefficient

variable (μ : Measure ℝ) (N : ℕ)

/-- A genuine bounded finite-coordinate synthesis map. -/
noncomputable def truncation (k : Fin N → Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℂ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi (fun n : Fin N =>
    InnerProductSpace.innerSL ℂ (k n))

/-- The n-th coordinate is the explicit L² Riesz inner product. -/
theorem truncation_apply (k : Fin N → Lp ℂ 2 μ)
    (f : Lp ℂ 2 μ) (n : Fin N) :
    truncation μ N k f n = inner ℂ (k n) f := by
  rfl

/-- Every finite-coordinate bounded truncation is compact, because
its codomain is finite-dimensional. -/
theorem truncation_compact (k : Fin N → Lp ℂ 2 μ) :
    IsCompactOperator (truncation μ N k) := by
  exact isCompactOperator_of_locallyCompactSpace_dom (truncation μ N k)

#print axioms GegenbauerFock.FiniteCoefficient.truncation_apply
#print axioms GegenbauerFock.FiniteCoefficient.truncation_compact

end GegenbauerFock.FiniteCoefficient
