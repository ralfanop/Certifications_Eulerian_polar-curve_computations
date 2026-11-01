import GegenbauerFock.PhyslibGeneralHSProductTraceClass

/-!
# V007 — genuine CFC trace-norm upper bound for arbitrary S₂ products

For arbitrary Hilbert–Schmidt endomorphisms R,S of a complete complex
Hilbert space, the trace norm of R*S is bounded by two explicitly
summable squared Hilbert–Schmidt row energies, on ANY complete Hilbert
basis. This is a genuine CFC absolute-value trace-norm statement.

The polar factor U of R*S provides
  |R*S| = U†*R*S;
Cauchy–Schwarz and the elementary inequality ab ≤ a²+b² bound each
positive trace diagonal. A separate basis-independent Schatten-Hölder
step will optimize the bound into ‖R‖₂*‖S‖₂, and eventually the sharp
two-sided trace-norm ideal bound.

No axiom, sorry, toolchain change, or modification to earlier proofs.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Genuine CFC trace norm of a general HS product is bounded by
two summable basis energies, with no positivity or finite-dimensional
hypothesis. The basis b is arbitrary and complete. -/
theorem traceNorm_mul_twoHilbertSchmidt_le_polar_energy
    (R S : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    traceNorm (R * S) (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
      (∑' i : w,
        ‖R.adjoint ((Polar.polarFactor (R * S)) (b i))‖ ^ 2) +
      (∑' i : w, ‖S (b i)‖ ^ 2) := by
  let T : H →L[ℂ] H := R * S
  let U : H →L[ℂ] H := Polar.polarFactor T
  let A : H →L[ℂ] H := R.adjoint.comp U
  let hT : IsTraceClass T :=
    isTraceClass_mul_of_twoHilbertSchmidt R S hR hS
  have hA : HilbertSchmidt.IsHilbertSchmidt A :=
    HilbertSchmidt.isHilbertSchmidt_comp_right R.adjoint
      (HilbertSchmidt.isHilbertSchmidt_adjoint R hR) U
  have hAs : Summable (fun i : w => ‖A (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hA
  have hSs : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  have hpolar : U.adjoint.comp T = CFC.abs T := by
    have h := Polar.star_polarFactor_mul_self T
    change star U * T = CFC.abs T at h
    simpa only [ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.mul_def] using h
  have hdiag (i : w) :
      inner ℂ (b i) (CFC.abs T (b i)) =
        inner ℂ (A (b i)) (S (b i)) := by
    calc
      inner ℂ (b i) (CFC.abs T (b i)) =
          inner ℂ (b i) (U.adjoint (R (S (b i)))) := by
        rw [← hpolar]
        rfl
      _ = inner ℂ (U (b i)) (R (S (b i))) :=
        ContinuousLinearMap.adjoint_inner_right U (b i) (R (S (b i)))
      _ = inner ℂ (R.adjoint (U (b i))) (S (b i)) :=
        (ContinuousLinearMap.adjoint_inner_left R (S (b i)) (U (b i))).symm
      _ = inner ℂ (A (b i)) (S (b i)) := rfl
  have hpoint (i : w) :
      (inner ℂ (b i) (CFC.abs T (b i))).re ≤
        ‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2 := by
    rw [hdiag i]
    have hcauchy :
        (inner ℂ (A (b i)) (S (b i))).re ≤
          ‖A (b i)‖ * ‖S (b i)‖ :=
      (Complex.re_le_norm _).trans
        (norm_inner_le_norm (A (b i)) (S (b i)))
    nlinarith [sq_nonneg (‖A (b i)‖ - ‖S (b i)‖),
      sq_nonneg (‖A (b i)‖ + ‖S (b i)‖)]
  rw [traceNorm_eq_of_hilbertBasis hT b]
  change (∑' i : w, (inner ℂ (b i) (CFC.abs T (b i))).re) ≤
    (∑' i : w, ‖A (b i)‖ ^ 2) +
    (∑' i : w, ‖S (b i)‖ ^ 2)
  calc
    (∑' i : w, (inner ℂ (b i) (CFC.abs T (b i))).re) ≤
        ∑' i : w, (‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2) :=
      Summable.tsum_le_tsum hpoint
        (summable_inner_abs_of_hilbertBasis hT b) (hAs.add hSs)
    _ = (∑' i : w, ‖A (b i)‖ ^ 2) +
        (∑' i : w, ‖S (b i)‖ ^ 2) :=
      hAs.tsum_add hSs

#print axioms ProbabilisticTheory.traceNorm_mul_twoHilbertSchmidt_le_polar_energy

end ProbabilisticTheory
