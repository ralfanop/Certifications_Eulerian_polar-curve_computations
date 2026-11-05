import GegenbauerFock.UltrasphericalSturmLiouvilleRealL2Kernel

/-!
# V007 — genuine well-defined Sturm action on the polynomial L² image

Define an actual map from the true polynomial-image submodule
of L²(νλ;ℝ) into itself by choosing a representing polynomial and
applying the certified differential expression.

The prior kernel-invariance theorem makes this action independent
of the choice. The same certified real Hilbert Green identity
proves symmetry of the domain action.

The next step is a linear-map structure and density of this domain;
we do not claim closure, essential self-adjointness or compact resolvent.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- A chosen real-polynomial representative of each actual L²
vector in the image of the polynomial evaluation linear map. -/
noncomputable def sturmRealDomainRepresentative
    (lam : ℝ) (hlam : 0 < lam)
    (x : sturmRealPolynomialDomain lam hlam) : ℝ[X] :=
  Classical.choose x.property

theorem sturmRealDomainRepresentative_spec
    (lam : ℝ) (hlam : 0 < lam)
    (x : sturmRealPolynomialDomain lam hlam) :
    sturmRealPolynomialLp lam hlam
        (sturmRealDomainRepresentative lam hlam x) =
      (x : Lp ℝ 2 (measure lam)) := by
  change sturmRealPolynomialLinear lam hlam
    (Classical.choose x.property) = x.val
  exact Classical.choose_spec x.property

/-- Differential action on the actual weighted-real-L²
polynomial-image domain. Kernel invariance ensures it does
not depend on the selected representative. -/
noncomputable def sturmRealDomainOperator
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPolynomialDomain lam hlam →
      sturmRealPolynomialDomain lam hlam :=
  fun x => ⟨sturmRealPolynomialLp lam hlam
      (sturmPolynomial lam (sturmRealDomainRepresentative lam hlam x)),
    ⟨sturmPolynomial lam (sturmRealDomainRepresentative lam hlam x),
      rfl⟩⟩

/-- Actual real L² domain action on a polynomial vector is
independent of the chosen representative. -/
theorem sturmRealDomainOperator_on_polynomial
    (lam : ℝ) (hlam : 0 < lam) (p : ℝ[X]) :
    sturmRealDomainOperator lam hlam
        ⟨sturmRealPolynomialLp lam hlam p,
          sturmRealPolynomialLp_mem_domain lam hlam p⟩ =
      ⟨sturmRealPolynomialLp lam hlam (sturmPolynomial lam p),
        sturmRealPolynomialLp_mem_domain lam hlam
          (sturmPolynomial lam p)⟩ := by
  apply Subtype.ext
  exact sturmRealPolynomialLp_action_well_defined lam hlam
    (sturmRealDomainRepresentative lam hlam
      ⟨sturmRealPolynomialLp lam hlam p,
        sturmRealPolynomialLp_mem_domain lam hlam p⟩)
    p (by
      simpa using sturmRealDomainRepresentative_spec lam hlam
        ⟨sturmRealPolynomialLp lam hlam p,
          sturmRealPolynomialLp_mem_domain lam hlam p⟩)

/-- The genuine polynomial-domain differential action satisfies
Green symmetry in the true real weighted-L² Hilbert product. -/
theorem sturmRealDomainOperator_symmetric
    (lam : ℝ) (hlam : 0 < lam)
    (x y : sturmRealPolynomialDomain lam hlam) :
    inner ℝ
        ((sturmRealDomainOperator lam hlam x :
          sturmRealPolynomialDomain lam hlam) : Lp ℝ 2 (measure lam))
        (y : Lp ℝ 2 (measure lam)) =
      inner ℝ
        (x : Lp ℝ 2 (measure lam))
        ((sturmRealDomainOperator lam hlam y :
          sturmRealPolynomialDomain lam hlam) : Lp ℝ 2 (measure lam)) := by
  let p := sturmRealDomainRepresentative lam hlam x
  let q := sturmRealDomainRepresentative lam hlam y
  have hx : sturmRealPolynomialLp lam hlam p =
      (x : Lp ℝ 2 (measure lam)) :=
    sturmRealDomainRepresentative_spec lam hlam x
  have hy : sturmRealPolynomialLp lam hlam q =
      (y : Lp ℝ 2 (measure lam)) :=
    sturmRealDomainRepresentative_spec lam hlam y
  change inner ℝ
    (sturmRealPolynomialLp lam hlam (sturmPolynomial lam p))
    (y : Lp ℝ 2 (measure lam)) =
    inner ℝ
      (x : Lp ℝ 2 (measure lam))
      (sturmRealPolynomialLp lam hlam (sturmPolynomial lam q))
  rw [← hx, ← hy]
  exact sturmRealPolynomialLp_green_inner_symm lam hlam p q

#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainRepresentative_spec
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainOperator_on_polynomial
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainOperator_symmetric

end GegenbauerFock.Ultraspherical
