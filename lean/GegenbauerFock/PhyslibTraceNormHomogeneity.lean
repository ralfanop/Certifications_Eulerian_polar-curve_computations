/-
Copyright (c) 2026 Tom Ole Diem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted for V007 from PhyslibAlpha TraceClass/Banach.lean.
-/
import GegenbauerFock.PhyslibTraceBasisIndependence

/-!
# V007 — true trace norm homogeneity for arbitrary trace-class operators

Beyond the scalar closure of the trace-class membership predicate,
this module proves the exact *norm* scaling under arbitrary complex
scalars using basis independence. No generic triangle inequality or
normed-group/Banach structure is assumed.
-/

noncomputable section
namespace ProbabilisticTheory
open scoped ComplexOrder InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

lemma traceNorm_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    traceNorm (c • T) (isTraceClass_smul c hT) = ‖c‖ * traceNorm T hT := by
  set w₀ : Set H := hT.choose with hw₀
  set b₀ : HilbertBasis w₀ ℂ H := hT.choose_spec.choose with hb₀def
  have habs : CFC.abs (c • T) = ‖c‖ • CFC.abs T := CFC.abs_smul c T
  have heq : ∀ i : w₀, (⟪b₀ i, CFC.abs (c • T) (b₀ i)⟫_ℂ).re
      = ‖c‖ * (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := by
    intro i
    rw [habs, smul_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right]
    simp [Complex.mul_re]
  rw [traceNorm_eq_of_hilbertBasis (isTraceClass_smul c hT) b₀]
  calc ∑' i : w₀, (⟪b₀ i, CFC.abs (c • T) (b₀ i)⟫_ℂ).re
      = ∑' i : w₀, ‖c‖ * (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := tsum_congr heq
    _ = ‖c‖ * ∑' i : w₀, (⟪b₀ i, CFC.abs T (b₀ i)⟫_ℂ).re := tsum_mul_left
    _ = ‖c‖ * traceNorm T hT := rfl

/-- The CFC trace norm is invariant under negation for every
possibly non-self-adjoint trace-class bounded endomorphism. -/
theorem traceNorm_neg_of_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    traceNorm (-T) (isTraceClass_neg hT) = traceNorm T hT := by
  have h := traceNorm_smul (-1 : ℂ) hT
  simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using h

#print axioms ProbabilisticTheory.traceNorm_smul
#print axioms ProbabilisticTheory.traceNorm_neg_of_isTraceClass
end ProbabilisticTheory
