import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# V007 — passing to strongly convergent products with uniform contractions

Let T_k and U_k be actual bounded real-linear maps of a Banach
space, with ‖T_k‖≤1. If U_k f→y for a fixed f and T_k y→z,
then T_k(U_k f)→z. The proof isolates the error
T_k(U_k f-y), bounds it by ‖U_k f-y‖ and uses continuity of addition.

This lemma is the missing stability tool for passing the exact
Yosida exponential semigroup composition law to the strong limit.
It does not presuppose that the strong limit is an operator semigroup.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open Filter
open scoped Topology

/-- Products of a uniformly contractive operator sequence preserve
strong convergence of the moving input. -/
theorem strongLimit_product_of_uniform_contraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T U : ℕ → E →L[ℝ] E)
    (hT : ∀ k : ℕ, ‖T k‖ ≤ 1)
    (f y z : E)
    (hU : Tendsto (fun k : ℕ => U k f) atTop (𝓝 y))
    (hTy : Tendsto (fun k : ℕ => T k y) atTop (𝓝 z)) :
    Tendsto (fun k : ℕ => T k (U k f)) atTop (𝓝 z) := by
  have hnorm : Tendsto (fun k : ℕ => ‖U k f - y‖) atTop (𝓝 (0 : ℝ)) := by
    have h := (hU.sub tendsto_const_nhds).norm
    simpa only [sub_self, norm_zero] using h
  have hbound (k : ℕ) :
      ‖T k (U k f - y)‖ ≤ ‖U k f - y‖ := by
    calc
      ‖T k (U k f - y)‖ ≤ ‖T k‖ * ‖U k f - y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖U k f - y‖ :=
        mul_le_mul_of_nonneg_right (hT k) (norm_nonneg _)
      _ = ‖U k f - y‖ := one_mul _
  have herror : Tendsto
      (fun k : ℕ => T k (U k f - y))
      atTop (𝓝 (0 : E)) :=
    squeeze_zero_norm hbound hnorm
  have hsum : Tendsto
      (fun k : ℕ => T k y + T k (U k f - y))
      atTop (𝓝 z) := by
    simpa only [add_zero] using hTy.add herror
  have heq :
      (fun k : ℕ => T k (U k f)) =
      (fun k : ℕ => T k y + T k (U k f - y)) := by
    funext k
    rw [← map_add]
    congr 1
    abel
  rw [heq]
  exact hsum

#print axioms GegenbauerFock.Ultraspherical.strongLimit_product_of_uniform_contraction

end GegenbauerFock.Ultraspherical
