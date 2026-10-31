import GegenbauerFock.PhyslibHilbertSchmidtTwoSidedIdeal
import GegenbauerFock.PhyslibPolarFactorCompat

/-!
# V007 — general S₂ * S₂ to S₁ product bridge

The key genuinely nonpositive Schatten step: for arbitrary bounded
Hilbert--Schmidt endomorphisms R, S on a complete complex Hilbert space,
their composition is in the actual CFC absolute-value trace class.

Let T = R*S and let U be its polar factor. The identity
  |T| = U†*R*S
rewrites the i-th positive diagonal as an inner product between
  (R†*U)e_i and S e_i.
The first factor is S₂ by the abstract right ideal and adjoint laws;
the second is S₂ by hypothesis. Thus the diagonal is bounded by the
sum of the two square-summable energies. No finite-dimensionality,
positivity of R or S, or unproved trace-norm triangle inequality.

This module is a separately audited port of the general Physlib
Hilbert--Schmidt product argument. Its Lean CI must be green before the
result is called certified; no additional axioms are introduced.
-/

noncomputable section
namespace ProbabilisticTheory

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The product of two arbitrary actual Hilbert--Schmidt operators
is trace class according to Physlib's genuine CFC-absolute predicate. -/
theorem isTraceClass_mul_of_twoHilbertSchmidt
    (R S : H →L[ℂ] H)
    (hR : HilbertSchmidt.IsHilbertSchmidt R)
    (hS : HilbertSchmidt.IsHilbertSchmidt S) :
    IsTraceClass (R * S) := by
  let T : H →L[ℂ] H := R * S
  let U : H →L[ℂ] H := Polar.polarFactor T
  let A : H →L[ℂ] H := R.adjoint.comp U
  have hA : HilbertSchmidt.IsHilbertSchmidt A :=
    HilbertSchmidt.isHilbertSchmidt_comp_right R.adjoint
      (HilbertSchmidt.isHilbertSchmidt_adjoint R hR) U
  obtain ⟨w, b, hAsum⟩ := hA
  have hSsum : Summable (fun i : w => ‖S (b i)‖ ^ 2) :=
    HilbertSchmidt.summable_norm_sq_apply_of_hilbertBasis w b hS
  have hpos : 0 ≤ CFC.abs T := CFC.abs_nonneg T
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
  have hbound (i : w) :
      (inner ℂ (b i) (CFC.abs T (b i))).re ≤
        ‖A (b i)‖ ^ 2 + ‖S (b i)‖ ^ 2 := by
    rw [hdiag i]
    have hcauchy :
        (inner ℂ (A (b i)) (S (b i))).re ≤
          ‖A (b i)‖ * ‖S (b i)‖ :=
      (Complex.re_le_norm _).trans
        (norm_inner_le_norm (A (b i)) (S (b i)))
    have ha : 0 ≤ ‖A (b i)‖ := norm_nonneg _
    have hs : 0 ≤ ‖S (b i)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖A (b i)‖ - ‖S (b i)‖),
      mul_nonneg ha hs]
  have hdiagsum : Summable (fun i : w =>
      (inner ℂ (b i) (CFC.abs T (b i))).re) := by
    apply Summable.of_nonneg_of_le
    · intro i
      exact ((ContinuousLinearMap.nonneg_iff_isPositive).mp hpos).re_inner_nonneg_right (b i)
    · exact hbound
    · exact hAsum.add hSsum
  change IsTraceClass T
  exact ⟨w, b, hdiagsum⟩

#print axioms ProbabilisticTheory.isTraceClass_mul_of_twoHilbertSchmidt

end ProbabilisticTheory
