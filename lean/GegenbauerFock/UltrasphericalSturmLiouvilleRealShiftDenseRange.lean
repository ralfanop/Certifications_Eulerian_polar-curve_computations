import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedSymmetry
import GegenbauerFock.UltrasphericalSturmLiouvillePolynomialShiftSurjective

/-!
# V007 — genuinely dense shifted range of the real Sturm L² operator

Transfer the kernel-checked exact algebraic surjectivity of I-L on
ALL real polynomials to the genuine weighted real L² Hilbert space.
The unbounded partial operator acts exactly on its concrete polynomial
domain. Every such L² polynomial vector lies in its I-L image, and
that image is therefore dense in the full true weighted L² space.

This is a range-density certificate, NOT an assertion that the
unbounded operator is essentially self-adjoint or has a bounded
everywhere-defined inverse.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every genuine polynomial L² vector has an exact preimage under
the shifted *partially-defined* Sturm operator I-L. -/
theorem sturmRealPartialShift_polynomial_preimage
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    ∃ x : (sturmRealPartialOperator lam hlam).domain,
      (x : SturmH lam) - sturmRealPartialOperator lam hlam x =
        sturmRealPolynomialLp lam hlam p := by
  obtain ⟨q, hq⟩ := sturmShiftPolynomial_surjective lam hlam p
  let x : (sturmRealPartialOperator lam hlam).domain :=
    ⟨sturmRealPolynomialLp lam hlam q,
      sturmRealPolynomialLp_mem_domain lam hlam q⟩
  have hA :
      sturmRealPartialOperator lam hlam x =
        sturmRealPolynomialLp lam hlam (sturmPolynomial lam q) := by
    change (((sturmRealDomainOperator lam hlam
        (⟨sturmRealPolynomialLp lam hlam q,
          sturmRealPolynomialLp_mem_domain lam hlam q⟩ :
          sturmRealPolynomialDomain lam hlam)) :
          sturmRealPolynomialDomain lam hlam) : SturmH lam) = _
    exact congrArg Subtype.val
      (sturmRealDomainOperator_on_polynomial lam hlam q)
  refine ⟨x, ?_⟩
  change sturmRealPolynomialLp lam hlam q -
      sturmRealPartialOperator lam hlam x =
        sturmRealPolynomialLp lam hlam p
  rw [hA]
  calc
    sturmRealPolynomialLp lam hlam q -
        sturmRealPolynomialLp lam hlam (sturmPolynomial lam q) =
      sturmRealPolynomialLp lam hlam (q - sturmPolynomial lam q) := by
        simpa only [sturmRealPolynomialLinear_apply] using
          ((sturmRealPolynomialLinear lam hlam).map_sub q
            (sturmPolynomial lam q)).symm
    _ = sturmRealPolynomialLp lam hlam p := by
      change sturmRealPolynomialLp lam hlam (sturmShiftPolynomial lam q) =
        sturmRealPolynomialLp lam hlam p
      rw [hq]

/-- On the genuine, potentially unbounded, real L² Sturm polynomial
domain the image of I-L is DENSE in all weighted real L². -/
theorem sturmRealPartialShift_denseRange
    (lam : ℝ) (hlam : 0 < lam) :
    DenseRange (fun x : (sturmRealPartialOperator lam hlam).domain =>
      (x : SturmH lam) - sturmRealPartialOperator lam hlam x) := by
  have hdense : Dense
      (sturmRealPolynomialDomain lam hlam : Set (SturmH lam)) :=
    sturmRealPolynomialDomain_dense_set lam hlam
  have hsub :
      (sturmRealPolynomialDomain lam hlam : Set (SturmH lam)) ⊆
        Set.range (fun x : (sturmRealPartialOperator lam hlam).domain =>
          (x : SturmH lam) - sturmRealPartialOperator lam hlam x) := by
    intro y hy
    obtain ⟨p, hp⟩ :
        ∃ p : ℝ[X], sturmRealPolynomialLinear lam hlam p = y := hy
    obtain ⟨x, hx⟩ := sturmRealPartialShift_polynomial_preimage lam hlam p
    refine ⟨x, ?_⟩
    simpa only [sturmRealPolynomialLinear_apply] using hx.trans hp
  exact hdense.mono hsub

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialShift_polynomial_preimage
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialShift_denseRange

end GegenbauerFock.Ultraspherical
