import Mathlib

/-!
# V007: compact rank-N approximations into the infinite Fock coefficient Hilbert space

Given ANY bounded complex-linear coefficient functionals on a complex
normed space E, the first N coefficient vectors define an operator
E → ℓ²(ℕ, ℂ), with finite-dimensional range and hence compactness.

This formalizes each genuine codomain-infinite finite-rank approximation
but not convergence to the full Gegenbauer-Fock transform.
-/

open scoped ENNReal

namespace GegenbauerFock.FockFiniteRank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev FockCoefficients : Type := lp (fun _ : ℕ => ℂ) 2

/-- The n-th coordinate inclusion of the complex scalar line into Fock ℓ². -/
noncomputable def coordinateInclusion (n : ℕ) :
    ℂ →L[ℂ] FockCoefficients :=
  lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 n

/-- Each scalar coordinate inclusion is a compact operator. -/
theorem coordinateInclusion_compact (n : ℕ) :
    IsCompactOperator (coordinateInclusion n) := by
  exact isCompactOperator_of_locallyCompactSpace_rng (coordinateInclusion n)

/-- A single coefficient functional gives an actual compact rank-one map. -/
theorem single_coefficient_compact (n : ℕ) (k : E →L[ℂ] ℂ) :
    IsCompactOperator ((coordinateInclusion n).comp k) := by
  exact (coordinateInclusion_compact n).comp_clm k

/-- Finite-rank approximation with values in infinite-dimensional ℓ². -/
noncomputable def truncation (k : ℕ → E →L[ℂ] ℂ) (N : ℕ) :
    E →L[ℂ] FockCoefficients :=
  ∑ n ∈ Finset.range N, (coordinateInclusion n).comp (k n)

/-- Genuine compactness of every finite-rank coefficient truncation. -/
theorem truncation_compact (k : ℕ → E →L[ℂ] ℂ) (N : ℕ) :
    IsCompactOperator (truncation k N) := by
  unfold truncation
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simpa using (isCompactOperator_zero : IsCompactOperator
        (0 : E →L[ℂ] FockCoefficients))
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      exact (single_coefficient_compact n (k n)).add ih

#print axioms GegenbauerFock.FockFiniteRank.coordinateInclusion_compact
#print axioms GegenbauerFock.FockFiniteRank.single_coefficient_compact
#print axioms GegenbauerFock.FockFiniteRank.truncation_compact

end GegenbauerFock.FockFiniteRank
