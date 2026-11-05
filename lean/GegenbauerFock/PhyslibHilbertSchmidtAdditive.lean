/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Source adapted for pinned V007 from PhyslibAlpha TraceClass/HilbertSchmidt.lean.
-/
import GegenbauerFock.PhyslibTraceBasisIndependence
import GegenbauerFock.PhyslibHilbertSchmidtCompat
import Mathlib.Analysis.MeanInequalities

/-!
# V007 — additive Hilbert–Schmidt ideal algebra (general Hilbert endomorphisms)

The source-compatible Physlib predicate IsHilbertSchmidt was already
ported. These actual basis-change identities and scalar/additive
closure theorems form a prerequisite for the nonpositive S₁ product
and additive closure, without claiming that latter theorem yet.
-/

noncomputable section
namespace ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]
namespace HilbertSchmidt

lemma hasSum_norm_sq_apply_eq_adjoint {S : H →L[ℂ] H}
    {w w' : Set H} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2)
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hcol : ∀ j : w', HasSum (fun i : w => F i j)
      (‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint S) (c j), b i⟫_ℂ := fun i =>
      (ContinuousLinearMap.adjoint_inner_left S (b i) (c j)).symm
    have key : (fun i : w => F i j) = fun i : w =>
        ‖⟪b i, (ContinuousLinearMap.adjoint S) (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) ((ContinuousLinearMap.adjoint S) (c j)),
        RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b ((ContinuousLinearMap.adjoint S) (c j))
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) = fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j = ∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j = ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 = ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm w' w) := by
      funext p; simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable
      (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' =>
        ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

lemma summable_norm_sq_adjoint_of_summable_norm_sq {S : H →L[ℂ] H}
    {w : Set H} (b : HilbertBasis w ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    Summable (fun i : w => ‖(ContinuousLinearMap.adjoint S) (b i)‖ ^ 2) :=
  (hasSum_norm_sq_apply_eq_adjoint b b hb).summable

lemma hasSum_norm_sq_apply_of_basis {S : H →L[ℂ] H} {w w' : Set H}
    (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2) (∑' i : w, ‖S (b i)‖ ^ 2) := by
  have hfirst := hasSum_norm_sq_apply_eq_adjoint b c hb
  have hstarc : Summable (fun j : w' => ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) :=
    hfirst.summable
  have hsecond := hasSum_norm_sq_apply_eq_adjoint (S := ContinuousLinearMap.adjoint S) c c hstarc
  have hsecond' : HasSum (fun j : w' => ‖S (c j)‖ ^ 2)
      (∑' j : w', ‖(ContinuousLinearMap.adjoint S) (c j)‖ ^ 2) := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hsecond
  rw [← hfirst.tsum_eq]
  exact hsecond'

lemma summable_norm_sq_apply_of_hilbertBasis {S : H →L[ℂ] H}
    (w : Set H) (b : HilbertBasis w ℂ H) (hS : IsHilbertSchmidt S) :
    Summable (fun i : w => ‖S (b i)‖ ^ 2) := by
  rcases hS with ⟨w₀, b₀, hb₀⟩
  exact (hasSum_norm_sq_apply_of_basis b₀ b hb₀).summable

lemma isHilbertSchmidt_zero : IsHilbertSchmidt (0 : H →L[ℂ] H) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  refine ⟨w, b, ?_⟩
  simp

omit [CompleteSpace H] in
lemma isHilbertSchmidt_smul {S : H →L[ℂ] H} (c : ℂ) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (c • S) := by
  rcases hS with ⟨w, b, hb⟩
  refine ⟨w, b, ?_⟩
  have hmul := hb.mul_left (‖c‖ ^ 2)
  apply hmul.congr
  intro i
  rw [smul_apply, norm_smul]
  ring

lemma isHilbertSchmidt_add {R S : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (R + S) := by
  rcases hR with ⟨w, b, hbR⟩
  have hSb : Summable (fun i : w => ‖S (b i)‖ ^ 2) := summable_norm_sq_apply_of_hilbertBasis w b hS
  refine ⟨w, b, ?_⟩
  apply Summable.of_nonneg_of_le (fun i => sq_nonneg _)
  · intro i
    have hnorm : ‖R (b i) + S (b i)‖ ≤ ‖R (b i)‖ + ‖S (b i)‖ := norm_add_le _ _
    have hsq : ‖R (b i) + S (b i)‖ ^ 2 ≤ (‖R (b i)‖ + ‖S (b i)‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 hnorm
    calc
      ‖(R + S) (b i)‖ ^ 2 = ‖R (b i) + S (b i)‖ ^ 2 := by rfl
      _ ≤ (‖R (b i)‖ + ‖S (b i)‖) ^ 2 := hsq
      _ ≤ 2 * ‖R (b i)‖ ^ 2 + 2 * ‖S (b i)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖R (b i)‖ - ‖S (b i)‖)]
  · exact (hbR.mul_left 2).add (hSb.mul_left 2)

lemma isHilbertSchmidt_sub {R S : H →L[ℂ] H}
    (hR : IsHilbertSchmidt R) (hS : IsHilbertSchmidt S) :
    IsHilbertSchmidt (R - S) := by
  simpa [sub_eq_add_neg] using isHilbertSchmidt_add hR (isHilbertSchmidt_smul (-1 : ℂ) hS)

#print axioms ProbabilisticTheory.HilbertSchmidt.hasSum_norm_sq_apply_eq_adjoint
#print axioms ProbabilisticTheory.HilbertSchmidt.hasSum_norm_sq_apply_of_basis
#print axioms ProbabilisticTheory.HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis
#print axioms ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_add
#print axioms ProbabilisticTheory.HilbertSchmidt.isHilbertSchmidt_sub

end HilbertSchmidt
end ProbabilisticTheory
