import Mathlib
import Manuscript13.EllisParsevalTonelli20261126
open Filter MeasureTheory
open scoped Topology
namespace Manuscript13.EllisCompactSpectrum20261127
noncomputable section
open Manuscript13.EllisGramKernelOperator20261124
open Manuscript13.EllisParsevalTonelli20261126

/-! Actual real Gram operator: trace-norm dominated rank-one expansion,
operator-norm compactness, and completeness of eigenspaces.
An ordinary countable Hilbert basis is used, not an eigenbasis.
-/
def rankTerm (v : H) : H →L[ℝ] H := (innerSL ℝ v).smulRight v

theorem rankTerm_apply (v x : H) : rankTerm v x = inner ℝ v x • v := rfl

theorem rankTerm_norm_le (v : H) : ‖rankTerm v‖ ≤ ‖v‖^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro x
  rw [rankTerm_apply, norm_smul]
  calc
    _ ≤ (‖v‖ * ‖x‖) * ‖v‖ :=
      mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
    _ = _ := by ring

theorem rankTerm_compact (v : H) : IsCompactOperator (rankTerm v : H → H) := by
  let C : ℝ →L[ℝ] H := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  have hC : IsCompactOperator (C : ℝ → H) := by
    first
    | exact isCompactOperator_of_locallyCompactSpace_dom C
    | exact isCompactOperator_of_locallyCompactSpace_dom (𝕜 := ℝ) (E := ℝ) C
    | exact?
  have h := hC.comp_clm (innerSL ℝ v)
  have he : (rankTerm v : H → H) = (C : ℝ → H) ∘ (innerSL ℝ v : H → ℝ) := by
    funext x
    rfl
  rw [he]
  exact h

theorem rank_series_summable (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    Summable (fun i => rankTerm (kernelOperator a κ ha hk (e i))) := by
  apply Summable.of_norm_bounded (kernel_hs_summable a κ ha hk e)
  intro i
  exact rankTerm_norm_le _

theorem rank_series_action (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) (x : H) :
    HasSum (fun i => rankTerm (kernelOperator a κ ha hk (e i)) x)
      (gramOperator a κ ha hk x) := by
  let A := kernelOperator a κ ha hk
  have h := e.hasSum_repr (A.adjoint x)
  have hm := A.hasSum h
  change HasSum (fun i => rankTerm (A (e i)) x) (A (A.adjoint x))
  convert hm using 1
  funext i
  rw [rankTerm_apply, map_smul, HilbertBasis.repr_apply_apply]
  congr 1
  calc
    inner ℝ (A (e i)) x = inner ℝ x (A (e i)) := real_inner_comm _ _
    _ = inner ℝ (A.adjoint x) (e i) := (A.adjoint_inner_left (e i) x).symm
    _ = inner ℝ (e i) (A.adjoint x) := real_inner_comm _ _

theorem rank_series_eq_gram (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    (∑' i, rankTerm (kernelOperator a κ ha hk (e i))) = gramOperator a κ ha hk := by
  apply ContinuousLinearMap.ext
  intro x
  have hs := (rank_series_summable a κ ha hk e).hasSum
  have h := (ContinuousLinearMap.apply ℝ H x).hasSum hs
  exact h.unique (rank_series_action a κ ha hk e x)

theorem gram_compact (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    IsCompactOperator (gramOperator a κ ha hk : H → H) := by
  have h := (rank_series_summable a κ ha hk e).hasSum
  rw [rank_series_eq_gram a κ ha hk e] at h
  apply isCompactOperator_of_tendsto h
  apply Filter.Eventually.of_forall
  intro s
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (rankTerm_compact _).add ih

theorem gram_symmetric (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ) :
    (gramOperator a κ ha hk : H →ₗ[ℝ] H).IsSymmetric := by
  intro x y
  simpa [gramOperator, Manuscript13.BirmanOperator20261124.gram] using
    Manuscript13.BirmanOperator20261124.gram_symmetric
      (kernelOperator a κ ha hk).adjoint x y

theorem eigenspaces_complete (a κ : ℝ) (ha : 0 < a) (hk : 0 < κ)
    (e : HilbertBasis ℕ ℝ H) :
    (⨆ μ : ℝ, Module.End.eigenspace (gramOperator a κ ha hk : H →ₗ[ℝ] H) μ)ᗮ = ⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (gram_compact a κ ha hk e) (gram_symmetric a κ ha hk)

end
end Manuscript13.EllisCompactSpectrum20261127
#print axioms Manuscript13.EllisCompactSpectrum20261127.rankTerm
#print axioms Manuscript13.EllisCompactSpectrum20261127.rankTerm_apply
#print axioms Manuscript13.EllisCompactSpectrum20261127.rankTerm_norm_le
#print axioms Manuscript13.EllisCompactSpectrum20261127.rankTerm_compact
#print axioms Manuscript13.EllisCompactSpectrum20261127.rank_series_summable
#print axioms Manuscript13.EllisCompactSpectrum20261127.rank_series_action
#print axioms Manuscript13.EllisCompactSpectrum20261127.rank_series_eq_gram
#print axioms Manuscript13.EllisCompactSpectrum20261127.gram_compact
#print axioms Manuscript13.EllisCompactSpectrum20261127.gram_symmetric
#print axioms Manuscript13.EllisCompactSpectrum20261127.eigenspaces_complete
