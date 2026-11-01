import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveShiftInjective

/-!
# V007 — exact positive polynomial-core resolvent as a linear equivalence

The genuine real weighted-L² polynomial submodule is invariant under
the differential Sturm expression. The preceding exact finite
polynomial inverse and Hilbert Green symmetry prove that EVERY t>0
gives a bijective shifted REAL LINEAR endomorphism tI-A on this
actual polynomial domain.

This is a linear equivalence on the dense polynomial-image submodule,
NOT a claim of a bounded inverse defined everywhere on full L².
The canonical graph closure and its resolvent need a separate proof.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The true real-linear shifted differential expression maps the
genuine polynomial L² image domain back into itself. -/
noncomputable def sturmRealDomainPositiveShift
    (lam t : ℝ) (hlam : 0 < lam) :
    sturmRealPolynomialDomain lam hlam →ₗ[ℝ]
      sturmRealPolynomialDomain lam hlam :=
  t • (LinearMap.id : sturmRealPolynomialDomain lam hlam →ₗ[ℝ]
    sturmRealPolynomialDomain lam hlam) -
    sturmRealDomainLinear lam hlam

theorem sturmRealDomainPositiveShift_injective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Injective (sturmRealDomainPositiveShift lam t hlam) := by
  intro x y hxy
  have hv := congrArg Subtype.val hxy
  have hshift :
      t • (x : SturmH lam) -
          sturmRealPartialOperator lam hlam x =
        t • (y : SturmH lam) -
          sturmRealPartialOperator lam hlam y := by
    simpa [sturmRealDomainPositiveShift,
      sturmRealPartialOperator_apply] using hv
  exact sturmRealPartialPositiveShift_injective lam t hlam ht hshift

theorem sturmRealDomainPositiveShift_surjective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Surjective (sturmRealDomainPositiveShift lam t hlam) := by
  intro y
  let p := sturmRealDomainRepresentative lam hlam y
  obtain ⟨x, hx⟩ :=
    sturmRealPartialPositiveShift_polynomial_preimage lam t hlam ht p
  refine ⟨x, ?_⟩
  apply Subtype.ext
  have hy : sturmRealPolynomialLp lam hlam p = (y : SturmH lam) :=
    sturmRealDomainRepresentative_spec lam hlam y
  change t • (x : SturmH lam) -
    sturmRealPartialOperator lam hlam x = (y : SturmH lam)
  exact hx.trans hy

/-- Every t>0 defines an exact linear equivalence on the genuine
real polynomial Sturm domain, with a finite polynomial inverse
for every polynomial representative. -/
noncomputable def sturmRealDomainPositiveShiftEquiv
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    sturmRealPolynomialDomain lam hlam ≃ₗ[ℝ]
      sturmRealPolynomialDomain lam hlam :=
  LinearEquiv.ofBijective (sturmRealDomainPositiveShift lam t hlam)
    ⟨sturmRealDomainPositiveShift_injective lam t hlam ht,
     sturmRealDomainPositiveShift_surjective lam t hlam ht⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainPositiveShift_injective
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainPositiveShift_surjective
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainPositiveShiftEquiv

end GegenbauerFock.Ultraspherical
