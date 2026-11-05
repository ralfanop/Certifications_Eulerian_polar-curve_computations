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
    innerSL ℂ (k n))

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

/-- The same finite truncation, now valued in the genuine
Euclidean *Hilbert* space with the ℓ² norm rather than the product norm. -/
noncomputable def hilbertTruncation (k : Fin N → Lp ℂ 2 μ) :
    Lp ℂ 2 μ →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℂ).symm.toContinuousLinearMap ∘L
    truncation μ N k

theorem hilbertTruncation_apply (k : Fin N → Lp ℂ 2 μ)
    (f : Lp ℂ 2 μ) (n : Fin N) :
    hilbertTruncation μ N k f n = inner ℂ (k n) f := by
  change truncation μ N k f n = inner ℂ (k n) f
  exact truncation_apply μ N k f n

/-- All finite Hilbert-space truncations are compact. This
assertion is about each N, NOT yet about the N → ∞ limit. -/
theorem hilbertTruncation_compact (k : Fin N → Lp ℂ 2 μ) :
    IsCompactOperator (hilbertTruncation μ N k) := by
  exact isCompactOperator_of_locallyCompactSpace_dom (hilbertTruncation μ N k)

/-- Quantitative Cauchy-Schwarz bound for the finite Hilbert
truncation. This is the exact finite-dimensional precursor of the
Hilbert-Schmidt norm identity, not the infinite-dimensional theorem. -/
theorem hilbertTruncation_energy_bound (k : Fin N → Lp ℂ 2 μ)
    (f : Lp ℂ 2 μ) :
    ‖hilbertTruncation μ N k f‖ ^ 2 ≤
      (∑ n : Fin N, ‖k n‖ ^ 2) * ‖f‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    (∑ n : Fin N, ‖hilbertTruncation μ N k f n‖ ^ 2)
        ≤ ∑ n : Fin N, (‖k n‖ * ‖f‖) ^ 2 := by
          apply Finset.sum_le_sum
          intro n hn
          rw [hilbertTruncation_apply]
          gcongr
          exact norm_inner_le_norm _ _
    _ = (∑ n : Fin N, ‖k n‖ ^ 2) * ‖f‖ ^ 2 := by
          simp_rw [mul_pow]
          rw [Finset.sum_mul]

#print axioms GegenbauerFock.FiniteCoefficient.truncation_apply
#print axioms GegenbauerFock.FiniteCoefficient.truncation_compact
#print axioms GegenbauerFock.FiniteCoefficient.hilbertTruncation_apply
#print axioms GegenbauerFock.FiniteCoefficient.hilbertTruncation_compact
#print axioms GegenbauerFock.FiniteCoefficient.hilbertTruncation_energy_bound

end GegenbauerFock.FiniteCoefficient
