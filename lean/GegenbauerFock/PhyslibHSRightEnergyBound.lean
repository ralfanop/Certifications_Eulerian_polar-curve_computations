/-
Copyright (c) 2026 Tom Ole Diem.
Released under Apache-2.0.
Adapted to V007's pinned Lean/Mathlib from
PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/HilbertSchmidt.lean.
-/
import GegenbauerFock.PhyslibHilbertSchmidtTwoSidedIdeal

/-!
# V007 — sharp Hilbert–Schmidt right-contraction energy estimate

For an arbitrary Hilbert–Schmidt endomorphism X and an operator W
of norm at most one, the squared HS energy of X*W does not exceed
the energy of X, on EVERY complete Hilbert basis. This is independent
of the Gegenbauer/Fock representation and is a required ingredient in
the trace-norm duality estimate.
-/

noncomputable section
namespace ProbabilisticTheory.HilbertSchmidt

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A bounded contraction on the right cannot increase the total
Hilbert–Schmidt square energy on any complete orthonormal basis. -/
theorem tsum_norm_sq_comp_right_le_of_opNorm_le_one
    {X W : H →L[ℂ] H} (hW : ‖W‖ ≤ 1)
    (hX : IsHilbertSchmidt X)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    (∑' i : w, ‖(X * W) (b i)‖ ^ 2) ≤
      ∑' i : w, ‖X (b i)‖ ^ 2 := by
  have hXW : IsHilbertSchmidt (X * W) := by
    change IsHilbertSchmidt (X.comp W)
    exact isHilbertSchmidt_comp_right X hX W
  have hXstar : IsHilbertSchmidt (ContinuousLinearMap.adjoint X) :=
    isHilbertSchmidt_adjoint X hX
  have hXWb : Summable (fun i : w => ‖(X * W) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hXW
  have hXb : Summable (fun i : w => ‖X (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hX
  have hstep1 :
      (∑' i : w, ‖(X * W) (b i)‖ ^ 2) =
      ∑' i : w, ‖(ContinuousLinearMap.adjoint (X * W)) (b i)‖ ^ 2 :=
    (hasSum_norm_sq_apply_eq_adjoint b b hXWb).tsum_eq.symm
  have hadj : ContinuousLinearMap.adjoint (X * W) =
      ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X := by
    show ContinuousLinearMap.adjoint (X ∘L W) = _
    rw [ContinuousLinearMap.adjoint_comp]
    rfl
  have hstep2 : ∀ i : w,
      ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X) (b i)‖ ≤
        ‖(ContinuousLinearMap.adjoint X) (b i)‖ := by
    intro i
    calc
      ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X) (b i)‖ =
          ‖(ContinuousLinearMap.adjoint W) ((ContinuousLinearMap.adjoint X) (b i))‖ := by
        rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
      _ ≤ ‖ContinuousLinearMap.adjoint W‖ *
          ‖(ContinuousLinearMap.adjoint X) (b i)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(ContinuousLinearMap.adjoint X) (b i)‖ := by
        have hWadj : ‖ContinuousLinearMap.adjoint W‖ ≤ 1 := by
          rw [(ContinuousLinearMap.adjoint).norm_map W]
          exact hW
        calc
          ‖ContinuousLinearMap.adjoint W‖ * ‖(ContinuousLinearMap.adjoint X) (b i)‖ ≤
              1 * ‖(ContinuousLinearMap.adjoint X) (b i)‖ :=
            mul_le_mul_of_nonneg_right hWadj (norm_nonneg _)
          _ = ‖(ContinuousLinearMap.adjoint X) (b i)‖ := one_mul _
  have hXstarb : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2) :=
    summable_norm_sq_apply_of_hilbertBasis w b hXstar
  have hcompareSummable : Summable (fun i : w =>
      ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X)
        (b i)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg _)
      (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hstep2 i))
      hXstarb
  have hcompare :
      (∑' i : w, ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X)
        (b i)‖ ^ 2) ≤
      ∑' i : w, ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2 :=
    hcompareSummable.tsum_le_tsum
      (fun i => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hstep2 i))
      hXstarb
  have hstep3 :
      (∑' i : w, ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2) =
      ∑' i : w, ‖X (b i)‖ ^ 2 :=
    (hasSum_norm_sq_apply_eq_adjoint b b hXb).tsum_eq
  calc
    (∑' i : w, ‖(X * W) (b i)‖ ^ 2) =
        ∑' i : w, ‖(ContinuousLinearMap.adjoint (X * W)) (b i)‖ ^ 2 := hstep1
    _ = ∑' i : w,
        ‖(ContinuousLinearMap.adjoint W * ContinuousLinearMap.adjoint X)
          (b i)‖ ^ 2 := by
      rw [hadj]
    _ ≤ ∑' i : w, ‖(ContinuousLinearMap.adjoint X) (b i)‖ ^ 2 :=
      hcompare
    _ = ∑' i : w, ‖X (b i)‖ ^ 2 := hstep3

#print axioms ProbabilisticTheory.HilbertSchmidt.tsum_norm_sq_comp_right_le_of_opNorm_le_one

end ProbabilisticTheory.HilbertSchmidt
