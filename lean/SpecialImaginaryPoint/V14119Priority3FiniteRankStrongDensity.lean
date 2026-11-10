import SpecialImaginaryPoint.V14119Priority3FiniteRankFredholm
import GegenbauerFock.PhyslibTraceClassHSFactorization
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Manuscript 14.119 Priority 3 — actual strong finite-rank approximation

For EVERY bounded complex endomorphism of the actual ℓ² Hilbert space,
define its concrete finite-rank Hilbert truncations as explicit finite
sums of rank-one maps. Hilbert-basis reconstruction proves their
pointwise strong convergence, and each truncation is compact via
a finite-dimensional scalar factorization.

We then construct finite-rank approximants of EVERY genuine
CFC-S₁ operator using its certified polar Hilbert–Schmidt
factorization T=R*S: the actual finite-rank maps R*P_N*S
converge strongly to T.

The topology is the STRONG operator topology. No theorem in
this module asserts S₁ norm convergence, operator norm convergence,
uniform determinant control, or the universal Fredholm determinant.
The next remaining obligation is the quantitative S₂ tail estimate.
-/

noncomputable section

namespace Manuscript14Priority3.FiniteRankDensity

open Filter Topology InnerProductSpace
open scoped ComplexOrder lp
open Manuscript14Priority3.TraceClassModel

/-- An explicit sum of N genuine Hilbert rank-one operators,
with the IMAGE vectors of the bounded map A. -/
def finiteBasisApprox (A : H →L[ℂ] H) (N : ℕ) : H →L[ℂ] H :=
  ∑ n ∈ Finset.range N, rankOne ℂ (A (b n)) (b n)

/-- Exact evaluation of the finite rank-one operator sum in terms
of the canonical Hilbert-basis coordinates. -/
theorem finiteBasisApprox_apply (A : H →L[ℂ] H) (N : ℕ) (x : H) :
    finiteBasisApprox A N x =
      ∑ n ∈ Finset.range N, (b.repr x n) • A (b n) := by
  classical
  calc
    finiteBasisApprox A N x =
        ∑ n ∈ Finset.range N, (rankOne ℂ (A (b n)) (b n)) x := by
          change (ContinuousLinearMap.apply ℂ H x)
            (∑ n ∈ Finset.range N, rankOne ℂ (A (b n)) (b n)) = _
          exact map_sum _ _ _
    _ = ∑ n ∈ Finset.range N, (b.repr x n) • A (b n) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp only [rankOne_apply, b.repr_apply_apply]

/-- For every bounded, even noncompact Hilbert operator, these
genuine rank-one finite partial sums converge strongly pointwise.
This is not operator-norm or trace-norm convergence. -/
theorem finiteBasisApprox_tendsto_apply
    (A : H →L[ℂ] H) (x : H) :
    Tendsto (fun N : ℕ => finiteBasisApprox A N x)
      atTop (𝓝 (A x)) := by
  have hsum :
      HasSum (fun n : ℕ => (b.repr x n) • A (b n)) (A x) := by
    simpa only [map_smul] using (b.hasSum_repr x).mapL A
  simpa only [finiteBasisApprox_apply] using hsum.tendsto_sum_nat

/-- A complex Hilbert rank-one map is compact as it factors
through the locally compact, one-dimensional complex scalar field. -/
theorem complexRankOne_compact (u v : H) :
    IsCompactOperator (rankOne ℂ u v : H →L[ℂ] H) := by
  have hspan : IsCompactOperator
      (ContinuousLinearMap.toSpanSingleton ℂ u : ℂ →L[ℂ] H) :=
    isCompactOperator_of_locallyCompactSpace_rng _
  have hcomp := hspan.comp_clm (innerSL ℂ v)
  change IsCompactOperator (fun x : H => inner ℂ v x • u) at hcomp
  change IsCompactOperator (fun x : H => inner ℂ v x • u)
  exact hcomp

/-- Every explicit N-term rank-one Hilbert approximant is compact.
This also explicitly provides a rank ≤ N algebraic representation. -/
theorem finiteBasisApprox_compact
    (A : H →L[ℂ] H) (N : ℕ) :
    IsCompactOperator (finiteBasisApprox A N) := by
  have hs (s : Finset ℕ) :
      IsCompactOperator
        (∑ n ∈ s, rankOne ℂ (A (b n)) (b n) : H →L[ℂ] H) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
    | @insert n s hn ih =>
        rw [Finset.sum_insert hn]
        change IsCompactOperator (fun x : H =>
          (rankOne ℂ (A (b n)) (b n)) x +
          (∑ i ∈ s, rankOne ℂ (A (b i)) (b i) : H →L[ℂ] H) x)
        exact (complexRankOne_compact (A (b n)) (b n)).add ih
  exact hs (Finset.range N)

/-- The finite orthogonal Hilbert-basis projection, as an
explicit sum of N rank-one orthogonal projections. -/
def finiteBasisProjection (N : ℕ) : H →L[ℂ] H :=
  finiteBasisApprox (1 : H →L[ℂ] H) N

theorem finiteBasisProjection_tendsto_apply (x : H) :
    Tendsto (fun N : ℕ => finiteBasisProjection N x)
      atTop (𝓝 x) := by
  simpa [finiteBasisProjection] using
    (finiteBasisApprox_tendsto_apply (1 : H →L[ℂ] H) x)

/-- Every projection P_N in the strong approximation family is
actually a finite sum of N rank-one, hence compact, Hilbert maps. -/
theorem finiteBasisProjection_compact (N : ℕ) :
    IsCompactOperator (finiteBasisProjection N) :=
  finiteBasisApprox_compact (1 : H →L[ℂ] H) N

/-- Actual finite-rank approximants for a general Hilbert operator
that admits a two-factor representation. -/
def factoredApprox (R S : H →L[ℂ] H) (N : ℕ) : H →L[ℂ] H :=
  R * finiteBasisProjection N * S

theorem factoredApprox_tendsto_apply
    (R S : H →L[ℂ] H) (x : H) :
    Tendsto (fun N : ℕ => factoredApprox R S N x)
      atTop (𝓝 ((R * S) x)) := by
  have hlim := finiteBasisProjection_tendsto_apply (S x)
  have hR : Tendsto
      (fun N : ℕ => R (finiteBasisProjection N (S x)))
      atTop (𝓝 (R (S x))) :=
    (R.continuous.tendsto (S x)).comp hlim
  simpa only [factoredApprox, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply] using hR

/-- True compactness of the finite-rank factored approximants:
compact operators form a two-sided ideal in bounded Hilbert maps. -/
theorem factoredApprox_compact
    (R S : H →L[ℂ] H) (N : ℕ) :
    IsCompactOperator (factoredApprox R S N) := by
  have h := finiteBasisProjection_compact N
  have hp := h.comp_clm S
  have hq := hp.clm_comp R
  change IsCompactOperator
    (fun x : H => R (finiteBasisProjection N (S x)))
  exact hq

/-- For EVERY actual genuine CFC-S₁ operator, its certified
Hilbert-Schmidt product factors provide a sequence of actual
compact finite-rank maps converging STRONGLY to the operator.
This is the nontrivial prerequisite before establishing S₁ density. -/
theorem traceClass_exists_strong_finiteRank_approx
    (T : ProbabilisticTheory.TraceClass H) :
    ∃ R S : H →L[ℂ] H,
      ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt R ∧
      ProbabilisticTheory.HilbertSchmidt.IsHilbertSchmidt S ∧
      R * S = T.1 ∧
      (∀ N : ℕ, IsCompactOperator (factoredApprox R S N)) ∧
      (∀ x : H,
        Tendsto (fun N : ℕ => factoredApprox R S N x)
          atTop (𝓝 (T.1 x))) := by
  obtain ⟨R, S, hR, hS, hRS⟩ :=
    ProbabilisticTheory.traceClass_exists_HS_mul_HS T.1 T.2
  refine ⟨R, S, hR, hS, hRS,
    fun N => factoredApprox_compact R S N, ?_⟩
  intro x
  rw [← hRS]
  exact factoredApprox_tendsto_apply R S x

#print axioms Manuscript14Priority3.FiniteRankDensity.finiteBasisApprox_apply
#print axioms Manuscript14Priority3.FiniteRankDensity.finiteBasisApprox_tendsto_apply
#print axioms Manuscript14Priority3.FiniteRankDensity.complexRankOne_compact
#print axioms Manuscript14Priority3.FiniteRankDensity.finiteBasisApprox_compact
#print axioms Manuscript14Priority3.FiniteRankDensity.finiteBasisProjection_tendsto_apply
#print axioms Manuscript14Priority3.FiniteRankDensity.finiteBasisProjection_compact
#print axioms Manuscript14Priority3.FiniteRankDensity.factoredApprox_tendsto_apply
#print axioms Manuscript14Priority3.FiniteRankDensity.factoredApprox_compact
#print axioms Manuscript14Priority3.FiniteRankDensity.traceClass_exists_strong_finiteRank_approx

end Manuscript14Priority3.FiniteRankDensity
