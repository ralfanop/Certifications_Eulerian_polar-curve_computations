import GegenbauerFock.PhyslibTraceClassHSFactorization
import GegenbauerFock.PhyslibHilbertSchmidtTwoSidedIdeal

/-!
# V007 — unrestricted addition of genuinely CFC trace-class operators

Every two trace-class bounded endomorphisms of an arbitrary complete
complex Hilbert space have a trace-class sum. No positivity, finite rank,
commutativity or shared-basis assumptions. This uses the independently
formalized polar decomposition, Hilbert–Schmidt factorization of each
trace-class summand, and the abstract two-sided Hilbert–Schmidt ideal.

The polar factor U of T + S gives |T + S| = U† (T + S).
For each summand X = R*Q, both R† U and Q are Hilbert–Schmidt, so the
conjugated diagonal is absolutely summable by the elementary estimate
|Re inner (R† U e_i) (Q e_i)| ≤ ‖R† U e_i‖² + ‖Q e_i‖².
Summing the two absolutely summable diagonals proves trace-class
membership of the sum without assuming an S₁ triangle inequality.

This candidate MUST pass an exact-SHA Lean build and #print axioms
audit before claiming certification.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- General complex trace-class operators are closed under addition.
The summands need not be positive or self-adjoint. -/
theorem isTraceClass_add_general
    (T S : H →L[ℂ] H) (hT : IsTraceClass T) (hS : IsTraceClass S) :
    IsTraceClass (T + S) := by
  let U : H →L[ℂ] H := Polar.polarFactor (T + S)
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ H
  have habs : U.adjoint.comp (T + S) = CFC.abs (T + S) := by
    have h := Polar.star_polarFactor_mul_self (T + S)
    change star U * (T + S) = CFC.abs (T + S) at h
    simpa only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def] using h
  have hpair : ∀ (X : H →L[ℂ] H), IsTraceClass X →
      Summable (fun i : w =>
        (inner ℂ (b i) ((U.adjoint.comp X) (b i))).re) := by
    intro X hX
    obtain ⟨R, Q, hR, hQ, hRQ⟩ :=
      traceClass_exists_HS_mul_HS X hX
    let A : H →L[ℂ] H := R.adjoint.comp U
    have hA : HilbertSchmidt.IsHilbertSchmidt A :=
      HilbertSchmidt.isHilbertSchmidt_comp_right R.adjoint
        (HilbertSchmidt.isHilbertSchmidt_adjoint R hR) U
    have hAsum : Summable (fun i : w => ‖A (b i)‖ ^ 2) :=
      HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hA
    have hQsum : Summable (fun i : w => ‖Q (b i)‖ ^ 2) :=
      HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hQ
    have hsum : Summable (fun i : w =>
        ‖A (b i)‖ ^ 2 + ‖Q (b i)‖ ^ 2) :=
      hAsum.add hQsum
    have hdiag (i : w) :
        inner ℂ (b i) ((U.adjoint.comp X) (b i)) =
          inner ℂ (A (b i)) (Q (b i)) := by
      calc
        inner ℂ (b i) ((U.adjoint.comp X) (b i)) =
            inner ℂ (b i) (U.adjoint (R (Q (b i)))) := by
              rw [← hRQ]
              rfl
        _ = inner ℂ (U (b i)) (R (Q (b i))) :=
          ContinuousLinearMap.adjoint_inner_right U (b i) (R (Q (b i)))
        _ = inner ℂ (R.adjoint (U (b i))) (Q (b i)) :=
          (ContinuousLinearMap.adjoint_inner_left R (Q (b i)) (U (b i))).symm
        _ = inner ℂ (A (b i)) (Q (b i)) := rfl
    apply Summable.of_norm_bounded hsum
    intro i
    rw [hdiag i]
    calc
      ‖(inner ℂ (A (b i)) (Q (b i))).re‖ ≤
          ‖inner ℂ (A (b i)) (Q (b i))‖ :=
        Complex.abs_re_le_norm _
      _ ≤ ‖A (b i)‖ * ‖Q (b i)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖A (b i)‖ ^ 2 + ‖Q (b i)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖A (b i)‖ - ‖Q (b i)‖)]
  have hpairT := hpair T hT
  have hpairS := hpair S hS
  have hpoint (i : w) :
      (inner ℂ (b i) (CFC.abs (T + S) (b i))).re =
        (inner ℂ (b i) ((U.adjoint.comp T) (b i))).re +
        (inner ℂ (b i) ((U.adjoint.comp S) (b i))).re := by
    rw [← habs]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      map_add, inner_add_right, Complex.add_re]
  refine ⟨w, b, ?_⟩
  exact (hpairT.add hpairS).congr (fun i => (hpoint i).symm)

#print axioms ProbabilisticTheory.isTraceClass_add_general

end ProbabilisticTheory
