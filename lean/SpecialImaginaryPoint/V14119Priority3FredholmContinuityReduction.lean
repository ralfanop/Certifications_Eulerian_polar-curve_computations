import SpecialImaginaryPoint.V14119Priority3S1Truncation
import SpecialImaginaryPoint.V14119Priority3OperatorCompression

/-!
# Manuscript 14.119 Priority 3 — Fredholm continuity reduction

This module isolates the remaining *operatorial* determinant obligation.

The actual Dirichlet spectral inverse is the underlying bounded operator
of a Banach sum in the genuine CFC-absolute Schatten S₁ space. Its
finite Hilbert-space compressions have certified complex matrix
determinants, converging to the Euler product.

We show that ANY complex-valued functional on the genuine S₁ Banach
space, continuous at this inverse and agreeing with the honest matrix
determinants on its finite S₁ truncations, MUST take the expected
Dirichlet value. The proof is independent of a hypothetical basis
choice for the functional.

IMPORTANT: No abstract Fredholm determinant is constructed here.
Existence, basis independence, trace-norm continuity, and the
finite-rank compatibility theorem for that functional are still open.
In particular, no relative zeta-determinant assertion is made.
-/

noncomputable section

namespace Manuscript14Priority3.TraceClassModel
open Filter Topology

/-- The *actual* CFC Schatten S₁ elements, rather than only their
underlying bounded operators, converge to their Banach sum. -/
theorem S1_compressions_tendsto :
    Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range N, S1term n :
          ProbabilisticTheory.TraceClass H))
      atTop
      (𝓝 (∑' n : ℕ, S1term n)) :=
  ProbabilisticTheory.TraceClass.partial_sums_tendsto_in_traceNorm
    S1term S1term_norm_summable

/-- A continuous functional agreeing on the actual finite Hilbert
compressions is forced to equal the certified Dirichlet product.
The continuity and finite-rank agreement are HYPOTHESES, not axioms
secretly defining a Fredholm determinant. -/
theorem continuous_functional_dirichlet_limit
    (F : ProbabilisticTheory.TraceClass H → ℂ)
    (x : ℝ) (hx : x ≠ 0)
    (hF : ContinuousAt F (∑' n : ℕ, S1term n))
    (hfinite : ∀ N : ℕ,
      F (∑ n ∈ Finset.range N, S1term n) =
        Matrix.det
          (Manuscript14Priority3.OperatorCompression.finiteOperatorShift
            N (x ^ 2))) :
    F (∑' n : ℕ, S1term n) = ((Real.sinh x / x : ℝ) : ℂ) := by
  have hmap :
      Tendsto
        (fun N : ℕ => F (∑ n ∈ Finset.range N, S1term n))
        atTop
        (𝓝 (F (∑' n : ℕ, S1term n))) :=
    hF.tendsto.comp S1_compressions_tendsto
  have hprod :=
    Manuscript14Priority3.OperatorCompression.finiteOperatorShift_det_tendsto
      x hx
  have heq :
      (fun N : ℕ => F (∑ n ∈ Finset.range N, S1term n)) =
        (fun N : ℕ =>
          Matrix.det
            (Manuscript14Priority3.OperatorCompression.finiteOperatorShift
              N (x ^ 2))) := by
    funext N
    exact hfinite N
  rw [heq] at hmap
  exact tendsto_nhds_unique hmap hprod

/-- Two functionals continuous at the true S₁ limit and agreeing
on every finite inverse truncation have equal values at the inverse.
This proves a uniqueness *reduction*, not existence. -/
theorem continuous_functionals_unique_at_inverse
    (F G : ProbabilisticTheory.TraceClass H → ℂ)
    (hF : ContinuousAt F (∑' n : ℕ, S1term n))
    (hG : ContinuousAt G (∑' n : ℕ, S1term n))
    (hfinite : ∀ N : ℕ,
      F (∑ n ∈ Finset.range N, S1term n) =
        G (∑ n ∈ Finset.range N, S1term n)) :
    F (∑' n : ℕ, S1term n) =
      G (∑' n : ℕ, S1term n) := by
  have hf :
      Tendsto
        (fun N : ℕ => F (∑ n ∈ Finset.range N, S1term n))
        atTop
        (𝓝 (F (∑' n : ℕ, S1term n))) :=
    hF.tendsto.comp S1_compressions_tendsto
  have hg :
      Tendsto
        (fun N : ℕ => G (∑ n ∈ Finset.range N, S1term n))
        atTop
        (𝓝 (G (∑' n : ℕ, S1term n))) :=
    hG.tendsto.comp S1_compressions_tendsto
  have heq :
      (fun N : ℕ => F (∑ n ∈ Finset.range N, S1term n)) =
        (fun N : ℕ => G (∑ n ∈ Finset.range N, S1term n)) := by
    funext N
    exact hfinite N
  rw [heq] at hf
  exact tendsto_nhds_unique hf hg

/-- A local trace-norm Lipschitz estimate for an eventual determinant
functional would immediately transfer the *already certified genuine S₁*
truncation bound to a determinant-error bound. The Lipschitz premise
remains a future theorem to establish for the constructed determinant. -/
theorem conditional_functional_error_le_tail
    (F : ProbabilisticTheory.TraceClass H → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hlocal : ∀ N : ℕ,
      ‖F (∑' n : ℕ, S1term n) -
        F (∑ n ∈ Finset.range N, S1term n)‖ ≤
        C * ProbabilisticTheory.TraceClass.traceNorm H
          ((∑' n : ℕ, S1term n) -
            (∑ n ∈ Finset.range N, S1term n)))
    (N : ℕ) :
    ‖F (∑' n : ℕ, S1term n) -
      F (∑ n ∈ Finset.range N, S1term n)‖ ≤
      C * ∑' k : ℕ, σ (k + N) := by
  exact (hlocal N).trans
    (mul_le_mul_of_nonneg_left (S1_truncation_traceNorm_le_tail N) hC)

#print axioms Manuscript14Priority3.TraceClassModel.S1_compressions_tendsto
#print axioms Manuscript14Priority3.TraceClassModel.continuous_functional_dirichlet_limit
#print axioms Manuscript14Priority3.TraceClassModel.continuous_functionals_unique_at_inverse
#print axioms Manuscript14Priority3.TraceClassModel.conditional_functional_error_le_tail

end Manuscript14Priority3.TraceClassModel
