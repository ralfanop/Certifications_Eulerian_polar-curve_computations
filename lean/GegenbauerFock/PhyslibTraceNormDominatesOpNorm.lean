/-
Copyright (c) 2026 Tom Ole Diem.
Released under Apache-2.0.
Adapted to V007's pinned Lean/Mathlib from
PhyslibAlpha/ProbabilisticTheory/HilbertSpace/TraceClass/Banach.lean.
-/
import GegenbauerFock.PhyslibTraceNormSqrtAbsEnergy

/-!
# V007 — operator norm bounded by the true CFC trace norm

For any (possibly non-selfadjoint) trace-class endomorphism on a complete
complex Hilbert space, the ambient bounded-operator norm is at most its
source-compatible Physlib trace norm. In particular the trace norm
is definite: it vanishes only at the zero operator.

The proof uses an all-bases Parseval identity, the positive square
root of |T| and the genuine basis-independent S₁ trace energy.
No assumption of the triangle inequality or Banach completeness.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The source-compatible CFC trace norm dominates operator norm
for every trace-class bounded Hilbert endomorphism. -/
theorem operatorNorm_le_traceNorm_via_sqrt_abs
    (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    ‖T‖ ≤ traceNorm T hT := by
  let A : H →L[ℂ] H := CFC.abs T
  let S : H →L[ℂ] H := CFC.sqrt A
  have hA : 0 ≤ A := CFC.abs_nonneg T
  have hSself : IsSelfAdjoint S :=
    IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA
  have hTA : ‖T‖ = ‖A‖ := (CFC.norm_abs).symm
  have hAeq : ‖A‖ = ‖S‖ ^ 2 := by
    rw [← hSS]
    exact hSself.norm_mul_self
  let w : Set H := hT.choose
  let b : HilbertBasis w ℂ H := hT.choose_spec.choose
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans hSself
  have hSum : Summable (fun i : w => ‖S (b i)‖ ^ 2) := by
    exact summable_sqrt_abs_basisEnergy T hT b
  have htrEq : traceNorm T hT =
      ∑' i : w, ‖S (b i)‖ ^ 2 :=
    traceNorm_eq_sqrt_abs_basisEnergy T hT b
  have htrNonneg : (0:ℝ) ≤ traceNorm T hT :=
    traceNorm_nonneg T hT
  have hbound : ∀ x : H,
      ‖S x‖ ^ 2 ≤ traceNorm T hT * ‖x‖ ^ 2 := by
    intro x
    have hpar : HasSum
        (fun i : w => ‖inner ℂ (b i) (S x)‖ ^ 2)
        (‖S x‖ ^ 2) :=
      hasSum_norm_sq_inner_basis b (S x)
    have heq2 (i : w) :
        inner ℂ (b i) (S x) = inner ℂ (S (b i)) x := by
      have h := ContinuousLinearMap.adjoint_inner_left S x (b i)
      rw [hSstar] at h
      exact h.symm
    have hpar' : HasSum
        (fun i : w => ‖inner ℂ (S (b i)) x‖ ^ 2)
        (‖S x‖ ^ 2) := by
      simpa [heq2] using hpar
    have hCS : ∀ i : w,
        ‖inner ℂ (S (b i)) x‖ ^ 2 ≤
          ‖S (b i)‖ ^ 2 * ‖x‖ ^ 2 := by
      intro i
      have h : ‖inner ℂ (S (b i)) x‖ ≤ ‖S (b i)‖ * ‖x‖ :=
        norm_inner_le_norm _ _
      calc
        ‖inner ℂ (S (b i)) x‖ ^ 2 ≤
            (‖S (b i)‖ * ‖x‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = ‖S (b i)‖ ^ 2 * ‖x‖ ^ 2 := by ring
    have hdom : HasSum
        (fun i : w => ‖S (b i)‖ ^ 2 * ‖x‖ ^ 2)
        (traceNorm T hT * ‖x‖ ^ 2) := by
      rw [htrEq]
      exact hSum.hasSum.mul_right (‖x‖ ^ 2)
    exact hasSum_le hCS hpar' hdom
  have hboundNorm : ∀ x : H,
      ‖S x‖ ≤ Real.sqrt (traceNorm T hT) * ‖x‖ := by
    intro x
    have h1 := hbound x
    have h2 : Real.sqrt (‖S x‖ ^ 2) ≤
        Real.sqrt (traceNorm T hT * ‖x‖ ^ 2) :=
      Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul htrNonneg,
      Real.sqrt_sq (norm_nonneg _)] at h2
  have hSnorm_le : ‖S‖ ≤ Real.sqrt (traceNorm T hT) :=
    S.opNorm_le_bound (Real.sqrt_nonneg _) hboundNorm
  have hSsq_le : ‖S‖ ^ 2 ≤ traceNorm T hT := by
    have h := pow_le_pow_left₀ (norm_nonneg S) hSnorm_le 2
    rwa [Real.sq_sqrt htrNonneg] at h
  rw [hTA, hAeq]
  exact hSsq_le

/-- Definiteness: vanishing of the true CFC trace norm forces
the underlying bounded operator to be identically zero. -/
theorem traceNorm_eq_zero_implies_operator_zero
    (T : H →L[ℂ] H) (hT : IsTraceClass T)
    (hzero : traceNorm T hT = 0) : T = 0 := by
  have hbound := operatorNorm_le_traceNorm_via_sqrt_abs T hT
  have hnorm : ‖T‖ = 0 := by
    apply le_antisymm
    · simpa [hzero] using hbound
    · exact norm_nonneg T
  exact norm_eq_zero.mp hnorm

#print axioms ProbabilisticTheory.operatorNorm_le_traceNorm_via_sqrt_abs
#print axioms ProbabilisticTheory.traceNorm_eq_zero_implies_operator_zero

end ProbabilisticTheory
