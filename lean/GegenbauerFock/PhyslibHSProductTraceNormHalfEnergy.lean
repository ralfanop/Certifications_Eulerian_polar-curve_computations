import GegenbauerFock.PhyslibHSProductTraceNormEnergy

/-!
# V007 — sharp Young-type polar estimate for CFC trace norm

For R,S genuinely Hilbert–Schmidt on an arbitrary complete complex
Hilbert space, and U the polar contraction of T=R*S, the positive
CFC trace norm satisfies

  2 * traceNorm(R*S) <= ∑ ||R† U eᵢ||² + ∑ ||S eᵢ||².

The improvement from the earlier coefficient 1 to 1/2 is necessary
for the sharp Schatten–Hölder inequality. This proof directly uses
the actual CFC.abs functional calculus, polar identity, and a common
complete Hilbert basis. It does not require or claim trace-norm
completeness of the source-compatible Physlib trace-class subtype.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem two_mul_traceNorm_mul_twoHilbertSchmidt_le_polar_energy
    (R S : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S)
    {w : Set H} (b : HilbertBasis w ℂ H) :
    2 * traceNorm (R * S)
      (isTraceClass_mul_of_twoHilbertSchmidt R S hR hS) ≤
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
  have hds : Summable (fun i : w =>
      (inner ℂ (b i) (CFC.abs T (b i))).re) :=
    summable_inner_abs_of_hilbertBasis hT b
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
      2 * (inner ℂ (b i) (CFC.abs T (b i))).re ≤
        ‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2 := by
    rw [hdiag i]
    have hcauchy :
        (inner ℂ (A (b i)) (S (b i))).re ≤
          ‖A (b i)‖ * ‖S (b i)‖ :=
      (Complex.re_le_norm _).trans
        (norm_inner_le_norm (A (b i)) (S (b i)))
    nlinarith [sq_nonneg (‖A (b i)‖ - ‖S (b i)‖)]
  change 2 * traceNorm T hT ≤
    (∑' i : w, ‖A (b i)‖ ^ 2) +
    (∑' i : w, ‖S (b i)‖ ^ 2)
  calc
    2 * traceNorm T hT =
        2 * ∑' i : w, (inner ℂ (b i) (CFC.abs T (b i))).re := by
          rw [traceNorm_eq_of_hilbertBasis hT b]
    _ = ∑' i : w,
        2 * (inner ℂ (b i) (CFC.abs T (b i))).re := by
          rw [tsum_mul_left]
    _ ≤ ∑' i : w,
        (‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2) :=
          (hds.mul_left 2).tsum_le_tsum hpoint (hAs.add hSs)
    _ = (∑' i : w, ‖A (b i)‖ ^ 2) +
        (∑' i : w, ‖S (b i)‖ ^ 2) :=
          hAs.tsum_add hSs

#print axioms ProbabilisticTheory.two_mul_traceNorm_mul_twoHilbertSchmidt_le_polar_energy

end ProbabilisticTheory
