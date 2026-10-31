import GegenbauerFock.UltrasphericalSturmLiouvilleRealShiftDenseRange
import GegenbauerFock.UltrasphericalSturmLiouvillePositiveShiftSurjective

/-!
# V007 — dense actual real L² range for EVERY positive spectral shift

The genuine polynomial differential operator is already realized
on its correct weighted real L² polynomial-image domain.

For every t>0, every real polynomial L² vector lies in the
exact image of tI-L on that actual domain, because the finite
polynomial shifted equation is algebraically surjective.
Since polynomial vectors are dense, the shifted image of the
actual unbounded operator is dense in the whole Hilbert space.

This does not claim that tI-L is already surjective onto all
L², boundedly invertible, or that its closure is self-adjoint.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every genuine polynomial weighted L² vector has an exact
preimage under tI-A on the original polynomial domain, t>0. -/
theorem sturmRealPartialPositiveShift_polynomial_preimage
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) (p : ℝ[X]) :
    ∃ x : (sturmRealPartialOperator lam hlam).domain,
      t • (x : SturmH lam) - sturmRealPartialOperator lam hlam x =
        sturmRealPolynomialLp lam hlam p := by
  obtain ⟨q, hq⟩ :=
    sturmPositiveShiftPolynomial_surjective lam t hlam ht p
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
  change t • sturmRealPolynomialLp lam hlam q -
      sturmRealPartialOperator lam hlam x =
        sturmRealPolynomialLp lam hlam p
  rw [hA]
  calc
    t • sturmRealPolynomialLp lam hlam q -
        sturmRealPolynomialLp lam hlam (sturmPolynomial lam q) =
        sturmRealPolynomialLp lam hlam (t • q) -
          sturmRealPolynomialLp lam hlam (sturmPolynomial lam q) := by
      rw [sturmRealPolynomialLp_smul]
    _ = sturmRealPolynomialLp lam hlam
          (t • q - sturmPolynomial lam q) := by
      simpa only [sturmRealPolynomialLinear_apply] using
        ((sturmRealPolynomialLinear lam hlam).map_sub
          (t • q) (sturmPolynomial lam q)).symm
    _ = sturmRealPolynomialLp lam hlam p := by
      change sturmRealPolynomialLp lam hlam
        (sturmPositiveShiftPolynomial lam t q) =
          sturmRealPolynomialLp lam hlam p
      rw [hq]

/-- The true real weighted-L² range of tI-A is dense for EVERY
positive real spectral shift, without any extra density axiom. -/
theorem sturmRealPartialPositiveShift_denseRange
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    DenseRange (fun x : (sturmRealPartialOperator lam hlam).domain =>
      t • (x : SturmH lam) - sturmRealPartialOperator lam hlam x) := by
  have hdense : Dense
      (sturmRealPolynomialDomain lam hlam : Set (SturmH lam)) :=
    sturmRealPolynomialDomain_dense_set lam hlam
  have hsub :
      (sturmRealPolynomialDomain lam hlam : Set (SturmH lam)) ⊆
        Set.range (fun x : (sturmRealPartialOperator lam hlam).domain =>
          t • (x : SturmH lam) - sturmRealPartialOperator lam hlam x) := by
    intro y hy
    obtain ⟨p, hp⟩ :
        ∃ p : ℝ[X], sturmRealPolynomialLinear lam hlam p = y := hy
    obtain ⟨x, hx⟩ :=
      sturmRealPartialPositiveShift_polynomial_preimage lam t hlam ht p
    refine ⟨x, ?_⟩
    simpa only [sturmRealPolynomialLinear_apply] using hx.trans hp
  exact hdense.mono hsub

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialPositiveShift_polynomial_preimage
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialPositiveShift_denseRange

end GegenbauerFock.Ultraspherical
