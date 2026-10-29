/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted for V007 from PhyslibAlpha.ProbabilisticTheory.HilbertSpace.TraceClass.Basic.
-/
import GegenbauerFock.PhyslibPositiveFixedBasis
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# V007 — source-compatible Physlib arbitrary-Hilbert-basis trace-norm invariance

Proof port from PhyslibAlpha Basic.lean (Apache-2.0); no upstream
import, no toolchain change. These results supply the *basis-independent*
CFC-absolute diagonal membership/norm API missing from the earlier
fixed-basis positive cone. They do not assert general S₁ addition,
triangle inequality or completion.
-/

noncomputable section
namespace ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **Parseval's identity**: `∑ᵢ |⟪eᵢ, y⟫|² = ‖y‖²` for a Hilbert basis `{eᵢ}`. -/
lemma hasSum_norm_sq_inner_basis {w : Type*} (b : HilbertBasis w ℂ H) (y : H) :
    HasSum (fun i : w => ‖⟪b i, y⟫_ℂ‖ ^ 2) (‖y‖ ^ 2) := by
  have h := b.hasSum_inner_mul_inner y y
  have hpt : ∀ i : w, ⟪y, b i⟫_ℂ * ⟪b i, y⟫_ℂ = ((‖⟪b i, y⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm y (b i), RCLike.conj_mul]
    norm_cast
  have hval : ⟪y, y⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; norm_cast
  simp_rw [hpt] at h
  rw [hval] at h
  exact Complex.hasSum_ofReal.mp h

/-- For self-adjoint `S`, the sum `∑ᵢ ‖S eᵢ‖²` does not depend on the Hilbert basis. -/
lemma hasSum_norm_sq_apply_of_selfAdjoint {S : H →L[ℂ] H} (hS : IsSelfAdjoint S)
    {w w' : Type*} (b : HilbertBasis w ℂ H) (c : HilbertBasis w' ℂ H)
    (hb : Summable (fun i : w => ‖S (b i)‖ ^ 2)) :
    HasSum (fun j : w' => ‖S (c j)‖ ^ 2) (∑' i : w, ‖S (b i)‖ ^ 2) := by
  classical
  set F : w → w' → ℝ := fun i j => ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 with hFdef
  have hFnonneg : 0 ≤ Function.uncurry F := fun _ => sq_nonneg _
  have hrow : ∀ i : w, HasSum (F i) (‖S (b i)‖ ^ 2) := fun i =>
    hasSum_norm_sq_inner_basis c (S (b i))
  have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
      S).symm.trans hS
  have hcol : ∀ j : w', HasSum (fun i : w => F i j) (‖S (c j)‖ ^ 2) := by
    intro j
    have e1 : ∀ i : w, ⟪c j, S (b i)⟫_ℂ = ⟪S (c j), b i⟫_ℂ := fun i => by
      have h1 := ContinuousLinearMap.adjoint_inner_left S (b i) (c j)
      rw [hSstar] at h1
      exact h1.symm
    have key : (fun i : w => F i j) = fun i : w => ‖⟪b i, S (c j)⟫_ℂ‖ ^ 2 := by
      funext i
      show ‖⟪c j, S (b i)⟫_ℂ‖ ^ 2 = _
      rw [e1 i, ← inner_conj_symm (b i) (S (c j)), RCLike.norm_conj]
    rw [key]
    exact hasSum_norm_sq_inner_basis b (S (c j))
  set G : w' → w → ℝ := fun j i => F i j with hGdef
  have hjoint : Summable (Function.uncurry F) := by
    rw [summable_prod_of_nonneg hFnonneg]
    refine ⟨fun i => (hrow i).summable, ?_⟩
    have heq : (fun i : w => ∑' j : w', F i j) = fun i : w => ‖S (b i)‖ ^ 2 :=
      funext fun i => (hrow i).tsum_eq
    show Summable fun i : w => ∑' j : w', F i j
    rwa [heq]
  have hswap := hjoint.tsum_comm' (fun i => (hrow i).summable) (fun j => (hcol j).summable)
  have hLHS : ∑' j : w', ∑' i : w, F i j = ∑' j : w', ‖S (c j)‖ ^ 2 :=
    tsum_congr fun j => (hcol j).tsum_eq
  have hRHS : ∑' i : w, ∑' j : w', F i j = ∑' i : w, ‖S (b i)‖ ^ 2 :=
    tsum_congr fun i => (hrow i).tsum_eq
  have hEq : ∑' j : w', ‖S (c j)‖ ^ 2 = ∑' i : w, ‖S (b i)‖ ^ 2 := by
    rw [← hLHS, ← hRHS]; exact hswap
  have hGnonneg : 0 ≤ Function.uncurry G := fun _ => sq_nonneg _
  have hjointG : Summable (Function.uncurry G) := by
    have hcomp : Function.uncurry G = Function.uncurry F ∘ (Equiv.prodComm w' w) := by
      funext p
      simp [Function.uncurry, hGdef, Equiv.prodComm]
    rw [hcomp]
    exact (Equiv.prodComm w' w).summable_iff.mpr hjoint
  have hcolSummable : Summable (fun j : w' => ‖S (c j)‖ ^ 2) := by
    have hpair := (summable_prod_of_nonneg hGnonneg).mp hjointG
    have h2 : Summable fun j : w' => ∑' i : w, G j i := by
      show Summable fun j : w' => ∑' i : w, Function.uncurry G (j, i)
      exact hpair.2
    have heq2 : (fun j : w' => ∑' i : w, G j i) = fun j : w' => ‖S (c j)‖ ^ 2 :=
      funext fun j => (hcol j).tsum_eq
    rwa [heq2] at h2
  rw [← hEq]
  exact hcolSummable.hasSum

lemma summable_inner_abs_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Type*}
    (b : HilbertBasis w ℂ H) :
    Summable (fun i => (⟪b i, CFC.abs T (b i)⟫_ℂ).re) := by
  obtain ⟨w₀, b₀, hb₀⟩ := h
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Type*} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S := (ContinuousLinearMap.star_eq_adjoint
          S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    have hval : ⟪S (b' i), S (b' i)⟫_ℂ = ((‖S (b' i)‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast
    rw [this, hval, Complex.ofReal_re]
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    simpa [hpt b₀] using hb₀
  have := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  simpa [hpt b] using this.summable

lemma traceNorm_eq_of_hilbertBasis {T : H →L[ℂ] H} (h : IsTraceClass T) {w : Type*}
    (b : HilbertBasis w ℂ H) :
    traceNorm T h = ∑' i, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
  let w₀ : Set H := h.choose
  let b₀ : HilbertBasis w₀ ℂ H := h.choose_spec.choose
  have hb₀ : Summable (fun i : w₀ => (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re) :=
    h.choose_spec.choose_spec
  set A : H →L[ℂ] H := CFC.abs T with hAdef
  have hAnonneg : 0 ≤ A := CFC.abs_nonneg T
  have hAself : IsSelfAdjoint A := .of_nonneg hAnonneg
  set S : H →L[ℂ] H := CFC.sqrt A with hSdef
  have hSself : IsSelfAdjoint S := .of_nonneg (CFC.sqrt_nonneg A)
  have hpt : ∀ {w' : Type*} (b' : HilbertBasis w' ℂ H) (i : w'),
      (⟪b' i, A (b' i)⟫_ℂ).re = ‖S (b' i)‖ ^ 2 := by
    intro w' b' i
    have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hAnonneg
    have hinner : ⟪b' i, A (b' i)⟫_ℂ = ⟪S (b' i), S (b' i)⟫_ℂ := by
      have hSstar : ContinuousLinearMap.adjoint S = S :=
        (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
      rw [← hSS]
      show ⟪b' i, (S * S) (b' i)⟫_ℂ = _
      rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      rw [← ContinuousLinearMap.adjoint_inner_left S (S (b' i)) (b' i), hSstar]
    rw [hinner, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hb₀' : Summable (fun i : w₀ => ‖S (b₀ i)‖ ^ 2) := by
    apply hb₀.congr
    intro i
    rw [hAdef, hpt]
  have hnorm := hasSum_norm_sq_apply_of_selfAdjoint hSself b₀ b hb₀'
  calc
    traceNorm T h = ∑' i : w₀, (⟪b₀ i, A (b₀ i)⟫_ℂ).re := by
      rfl
    _ = ∑' i : w₀, ‖S (b₀ i)‖ ^ 2 := by
      apply tsum_congr
      intro i
      exact hpt b₀ i
    _ = ∑' i : w, ‖S (b i)‖ ^ 2 := hnorm.tsum_eq.symm
    _ = ∑' i : w, (⟪b i, A (b i)⟫_ℂ).re := by
      apply tsum_congr
      intro i
      exact (hpt b i).symm
    _ = ∑' i, (⟪b i, CFC.abs T (b i)⟫_ℂ).re := by
      rfl

#print axioms ProbabilisticTheory.hasSum_norm_sq_inner_basis
#print axioms ProbabilisticTheory.hasSum_norm_sq_apply_of_selfAdjoint
#print axioms ProbabilisticTheory.summable_inner_abs_of_hilbertBasis
#print axioms ProbabilisticTheory.traceNorm_eq_of_hilbertBasis

end ProbabilisticTheory
