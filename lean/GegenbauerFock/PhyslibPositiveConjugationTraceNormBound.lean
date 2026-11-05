import GegenbauerFock.PhyslibPositiveTraceSqrtEnergy
import GegenbauerFock.PhyslibHSRightBasisEnergyBound
import GegenbauerFock.PhyslibTraceClassTwoSidedIdeal

/-!
# V007 — sharp positive trace-class conjugation ideal bound

For arbitrary positive trace-class T and arbitrary bounded B on any
complete complex Hilbert space H, this proves the actual CFC trace-norm
inequality for the positive conjugate B† T B:

  ‖B† T B‖₁ ≤ ‖B‖² ‖T‖₁.

The new result is independent of the Gegenbauer kernel and has no
finite-rank assumption. The general nonpositive A*T*B trace-norm bound
and the Banach-space completion remain separate obligations.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- General sharp positive S₁ ideal inequality in the genuine
CFC-absolute trace norm, on every complete complex Hilbert space. -/
theorem positive_traceNorm_conjugation_le
    (T : H →L[ℂ] H) (hpos : 0 ≤ T) (htr : IsTraceClass T)
    (B : H →L[ℂ] H) :
    traceNorm (B.adjoint * T * B)
      (isTraceClass_twoSided T htr B.adjoint B) ≤
      ‖B‖ ^ 2 * traceNorm T htr := by
  let S : H →L[ℂ] H := CFC.sqrt T
  have hSstar : ContinuousLinearMap.adjoint S = S :=
    (ContinuousLinearMap.star_eq_adjoint S).symm.trans
      (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg T))
  have hS : HilbertSchmidt.IsHilbertSchmidt S := by
    change HilbertSchmidt.IsHilbertSchmidt (CFC.sqrt T)
    simpa only [CFC.abs_of_nonneg T hpos] using
      (traceClass_sqrt_abs_isHS T htr)
  have hsquare : S * S = T := CFC.sqrt_mul_sqrt_self T hpos
  have hGram :
      B.adjoint * T * B =
        (S.comp B).adjoint.comp (S.comp B) := by
    rw [ContinuousLinearMap.adjoint_comp, hSstar]
    change B.adjoint * T * B = (B.adjoint * S) * (S * B)
    rw [← hsquare]
    simp only [mul_assoc]
  have hnonneg : 0 ≤ B.adjoint * T * B := by
    rw [hGram]
    exact (ContinuousLinearMap.nonneg_iff_isPositive).2
      (ContinuousLinearMap.isPositive_adjoint_comp_self (S.comp B))
  let hB : IsTraceClass (B.adjoint * T * B) :=
    isTraceClass_twoSided T htr B.adjoint B
  let b := hB.choose_spec.choose
  have hdiagonal (i : hB.choose) :
      (inner ℂ (b i) ((B.adjoint * T * B) (b i))).re =
        ‖(S.comp B) (b i)‖ ^ 2 := by
    have hinner :
        inner ℂ (b i) (((S.comp B).adjoint.comp (S.comp B)) (b i)) =
        inner ℂ ((S.comp B) (b i)) ((S.comp B) (b i)) := by
      change inner ℂ (b i)
        ((S.comp B).adjoint ((S.comp B) (b i))) = _
      exact ContinuousLinearMap.adjoint_inner_right
        (S.comp B) (b i) ((S.comp B) (b i))
    calc
      (inner ℂ (b i) ((B.adjoint * T * B) (b i))).re =
          (inner ℂ (b i)
            (((S.comp B).adjoint.comp (S.comp B)) (b i))).re :=
        congrArg (fun (K : H →L[ℂ] H) => (inner ℂ (b i) (K (b i))).re) hGram
      _ = ‖(S.comp B) (b i)‖ ^ 2 := by
        rw [hinner, inner_self_eq_norm_sq_to_K]
        norm_cast
  change traceNorm (B.adjoint * T * B) hB ≤ _
  calc
    traceNorm (B.adjoint * T * B) hB =
        ∑' i : hB.choose,
          (inner ℂ (b i) ((B.adjoint * T * B) (b i))).re :=
      traceNorm_eq_diagonal_of_nonneg (B.adjoint * T * B) hnonneg hB
    _ = ∑' i : hB.choose, ‖(S.comp B) (b i)‖ ^ 2 :=
      tsum_congr hdiagonal
    _ ≤ ‖B‖ ^ 2 * (∑' i : hB.choose, ‖S (b i)‖ ^ 2) :=
      HilbertSchmidt.right_basis_energy_le S hS B b
    _ = ‖B‖ ^ 2 * traceNorm T htr := by
      rw [← positive_traceNorm_eq_sqrt_basis_energy T hpos htr b]

#print axioms ProbabilisticTheory.positive_traceNorm_conjugation_le

end ProbabilisticTheory
