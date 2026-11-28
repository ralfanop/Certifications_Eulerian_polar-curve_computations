import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# The genuine diagonal trace of an absolutely nuclear Hilbert operator

This module starts from an actual operator-norm rank-one expansion and
an absolutely summable nuclear cost. It proves absolute summability of
the diagonal on every Hilbert basis, its equality with the nuclear
pairing sum, basis independence, and the nuclear-cost bound. No scalar
trace is stipulated to equal an operator trace.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SharedCore.NuclearDiagonalTrace

open InnerProductSpace
open scoped InnerProductSpace

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- Absolute Parseval pairing, with the sharp Cauchy--Schwarz bound. -/
theorem pairing_abs_summable_bound (b : HilbertBasis κ ℂ E) (u v : E) :
    Summable (fun j => ‖⟪v, b j⟫_ℂ * ⟪b j, u⟫_ℂ‖) ∧
      (∑' j, ‖⟪v, b j⟫_ℂ * ⟪b j, u⟫_ℂ‖) ≤ ‖u‖ * ‖v‖ := by
  have h := lp.tsum_mul_le_mul_norm
    (by simpa using Real.HolderConjugate.two_two) (b.repr v) (b.repr u)
  simpa only [HilbertBasis.repr_apply_apply, norm_mul, norm_inner_symm,
    LinearIsometryEquiv.norm_map, mul_comm] using h

/-- The nuclear pairing is absolutely summable. -/
theorem nuclear_pairing_summable (u v : ι → E)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun i => ⟪v i, u i⟫_ℂ) := by
  apply Summable.of_norm_bounded hcost
  intro i
  simpa only [mul_comm] using norm_inner_le_norm (v i) (u i)

/-- The double series needed to interchange a nuclear expansion and a
Hilbert-basis diagonal is absolutely summable. -/
theorem nuclear_diagonal_double_abs_summable
    (b : HilbertBasis κ ℂ E) (u v : ι → E)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖)) :
    Summable (fun p : ι × κ => ‖⟪v p.1, b p.2⟫_ℂ * ⟪b p.2, u p.1⟫_ℂ‖) := by
  rw [summable_prod_of_nonneg (fun _ => norm_nonneg _)]
  refine ⟨fun i => (pairing_abs_summable_bound b (u i) (v i)).1, ?_⟩
  apply Summable.of_nonneg_of_le
  · intro i
    exact tsum_nonneg (fun j => norm_nonneg _)
  · intro i
    exact (pairing_abs_summable_bound b (u i) (v i)).2
  · exact hcost

/-- On any Hilbert basis, the diagonal of the actual nuclear operator
has the nuclear pairing sum. This proves that the value is intrinsic. -/
theorem nuclear_diagonal_hasSum
    (b : HilbertBasis κ ℂ E) (u v : ι → E)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖))
    (T : E →L[ℂ] E)
    (hT : (∑' i, rankOne ℂ (u i) (v i)) = T) :
    HasSum (fun j => ⟪b j, T (b j)⟫_ℂ) (∑' i, ⟪v i, u i⟫_ℂ) := by
  let f : ι × κ → ℂ := fun p => ⟪v p.1, b p.2⟫_ℂ * ⟪b p.2, u p.1⟫_ℂ
  have hf : Summable f := (nuclear_diagonal_double_abs_summable b u v hcost).of_norm
  have hop : Summable (fun i => rankOne ℂ (u i) (v i)) := by
    apply Summable.of_norm
    simpa only [norm_rankOne] using hcost
  have hdiag (j : κ) : (∑' i, f (i, j)) = ⟪b j, T (b j)⟫_ℂ := by
    have heval := (hop.hasSum.mapL (ContinuousLinearMap.apply ℂ E (b j))).mapL (innerSL ℂ (b j))
    rw [hT] at heval
    simpa only [f, ContinuousLinearMap.apply_apply, innerSL_apply_apply,
      rankOne_apply, inner_smul_right] using heval.tsum_eq
  have hrow (i : ι) : (∑' j, f (i, j)) = ⟪v i, u i⟫_ℂ :=
    b.tsum_inner_mul_inner (v i) (u i)
  have hs : Summable (fun j => ∑' i, f (i, j)) := hf.prod_symm.prod
  have heq : (∑' j, ∑' i, f (i, j)) = ∑' i, ⟪v i, u i⟫_ℂ := by
    have hswap : (∑' j, ∑' i, f (i, j)) = ∑' i, ∑' j, f (i, j) :=
      hf.tsum_comm' (fun i => hf.prod_factor i) (fun j => hf.prod_symm.prod_factor j)
    exact hswap.trans (tsum_congr hrow)
  have hsum := hs.hasSum
  rw [heq] at hsum
  simpa only [hdiag] using hsum

/-- Absolute diagonal summability, not just a conditionally convergent
sum of the diagonal entries. -/
theorem nuclear_diagonal_abs_summable
    (b : HilbertBasis κ ℂ E) (u v : ι → E)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖))
    (T : E →L[ℂ] E)
    (hT : (∑' i, rankOne ℂ (u i) (v i)) = T) :
    Summable (fun j => ‖⟪b j, T (b j)⟫_ℂ‖) :=
  (nuclear_diagonal_hasSum b u v hcost T hT).summable.norm

/-- Sharp nuclear-cost bound for the genuine basis trace. -/
theorem nuclear_diagonal_norm_le
    (b : HilbertBasis κ ℂ E) (u v : ι → E)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖))
    (T : E →L[ℂ] E)
    (hT : (∑' i, rankOne ℂ (u i) (v i)) = T) :
    ‖∑' j, ⟪b j, T (b j)⟫_ℂ‖ ≤ ∑' i, ‖u i‖ * ‖v i‖ := by
  rw [(nuclear_diagonal_hasSum b u v hcost T hT).tsum_eq]
  have hs := (nuclear_pairing_summable u v hcost).norm
  exact (norm_tsum_le_tsum_norm hs).trans
    (hs.tsum_le_tsum (fun i => by
      simpa only [mul_comm] using norm_inner_le_norm (v i) (u i)) hcost)

/-- The diagonal traces agree even for bases with different index types. -/
theorem nuclear_diagonal_basis_independent {κ' : Type*}
    (b : HilbertBasis κ ℂ E) (c : HilbertBasis κ' ℂ E) (u v : ι → E)
    (hcost : Summable (fun i => ‖u i‖ * ‖v i‖))
    (T : E →L[ℂ] E)
    (hT : (∑' i, rankOne ℂ (u i) (v i)) = T) :
    (∑' j, ⟪b j, T (b j)⟫_ℂ) = ∑' j, ⟪c j, T (c j)⟫_ℂ := by
  rw [(nuclear_diagonal_hasSum b u v hcost T hT).tsum_eq,
    (nuclear_diagonal_hasSum c u v hcost T hT).tsum_eq]

#print axioms pairing_abs_summable_bound
#print axioms nuclear_pairing_summable
#print axioms nuclear_diagonal_double_abs_summable
#print axioms nuclear_diagonal_hasSum
#print axioms nuclear_diagonal_abs_summable
#print axioms nuclear_diagonal_norm_le
#print axioms nuclear_diagonal_basis_independent

end SharedCore.NuclearDiagonalTrace
