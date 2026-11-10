import Mathlib

/-!
# Priority 3 — sharp first-order increment of finite principal-minor expansions

This isolates the combinatorial core of the trace-norm determinant
perturbation bound. For a complex-valued principal-minor weight f and
nonnegative nuclear costs c_i, insertion of a new rank-one index a
contributes exactly the sum of terms containing a.

If each such term is bounded by c_a times the remaining product costs,
then the increment is bounded by c_a exp(Σ_{i∈s} c_i), with no dimension
factorial. Unlike a pure scalar envelope, this is a complex cancellation
identity for the *difference of two full finite subset expansions*.

The eventual identification of these expansions with the intrinsic
finite nuclear Fredholm determinants is a separate algebraic bridge;
this file does not assert that all S₁ operators already have a
determinant functional.
-/

noncomputable section
namespace Manuscript14Priority3.MinorExpansionIncrement

variable {ι : Type*} [DecidableEq ι]

/-- A finite principal-subset polynomial expansion with complex weights. -/
def principalExpansion (f : Finset ι → ℂ) (s : Finset ι) : ℂ :=
  ∑ t ∈ s.powerset, f t

/-- Exact complex increment: inserting a new index contributes
precisely the subsets containing it, with no approximation. -/
theorem principalExpansion_insert_sub
    (f : Finset ι → ℂ) (s : Finset ι) (a : ι) (ha : a ∉ s) :
    principalExpansion f (insert a s) - principalExpansion f s =
      ∑ t ∈ s.powerset, f (insert a t) := by
  unfold principalExpansion
  rw [Finset.sum_powerset_insert ha]
  abel

/-- SHARP dimension-free first-order exponential bound on the
increment of a complex finite principal-minor expansion.

The explicit hypothesis is an inserted-minor cost control, which
must be instantiated from the unrestricted Gram–Hadamard theorem.
No determinant estimate is assumed as an axiom. -/
theorem principalExpansion_insert_norm_le_exp
    (f : Finset ι → ℂ) (s : Finset ι) (a : ι)
    (ha : a ∉ s) (c : ι → ℝ)
    (hc : ∀ i ∈ insert a s, 0 ≤ c i)
    (hinsert : ∀ t ∈ s.powerset,
      ‖f (insert a t)‖ ≤ c a * ∏ i ∈ t, c i) :
    ‖principalExpansion f (insert a s) - principalExpansion f s‖ ≤
      c a * Real.exp (∑ i ∈ s, c i) := by
  rw [principalExpansion_insert_sub f s a ha]
  have hbase : (∏ i ∈ s, (1 + c i)) ≤
      Real.exp (∑ i ∈ s, c i) := by
    exact Real.prod_one_add_le_exp_sum s
      (fun i hi => hc i (Finset.mem_insert_of_mem hi))
  calc
    ‖∑ t ∈ s.powerset, f (insert a t)‖ ≤
        ∑ t ∈ s.powerset, ‖f (insert a t)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ t ∈ s.powerset, c a * ∏ i ∈ t, c i := by
      apply Finset.sum_le_sum
      intro t ht
      exact hinsert t ht
    _ = c a * ∏ i ∈ s, (1 + c i) := by
      rw [Finset.mul_sum]
      congr 1
      simpa only using (Finset.prod_one_add (s := s) (f := c)).symm
    _ ≤ c a * Real.exp (∑ i ∈ s, c i) :=
      mul_le_mul_of_nonneg_left hbase (hc a (Finset.mem_insert_self a s))

#print axioms Manuscript14Priority3.MinorExpansionIncrement.principalExpansion_insert_sub
#print axioms Manuscript14Priority3.MinorExpansionIncrement.principalExpansion_insert_norm_le_exp

end Manuscript14Priority3.MinorExpansionIncrement
