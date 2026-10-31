import GegenbauerFock.UltrasphericalSturmLiouvilleRealDomainOperator

/-!
# V007 — real-linear Sturm operator on the genuine weighted-L² domain

The genuine polynomial-image domain has a well-defined differential
action because the already certified Hilbert Green identity makes the
polynomial-evaluation kernel invariant.

Prove additivity and scalar homogeneity by taking polynomial
representatives of actual L² domain vectors and using the
certified representation-independence lemma.

This constructs an actual real-linear (not necessarily bounded)
operator on the polynomial-image submodule. Density, graph closure,
essential self-adjointness, and nonzero resolvents remain to prove.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory Polynomial

/-- Additivity of the domain action is independent of representative
choices because the evaluation kernel is invariant under Sturm. -/
theorem sturmRealDomainOperator_add
    (lam : ℝ) (hlam : 0 < lam)
    (x y : sturmRealPolynomialDomain lam hlam) :
    sturmRealDomainOperator lam hlam (x + y) =
      sturmRealDomainOperator lam hlam x +
        sturmRealDomainOperator lam hlam y := by
  let p := sturmRealDomainRepresentative lam hlam x
  let q := sturmRealDomainRepresentative lam hlam y
  let r := sturmRealDomainRepresentative lam hlam (x + y)
  have hr :
      sturmRealPolynomialLp lam hlam r =
        sturmRealPolynomialLp lam hlam (p + q) := by
    calc
      sturmRealPolynomialLp lam hlam r =
          ((x + y : sturmRealPolynomialDomain lam hlam) :
            Lp ℝ 2 (measure lam)) :=
        sturmRealDomainRepresentative_spec lam hlam (x + y)
      _ = (x : Lp ℝ 2 (measure lam)) +
          (y : Lp ℝ 2 (measure lam)) := rfl
      _ = sturmRealPolynomialLp lam hlam p +
          sturmRealPolynomialLp lam hlam q := by
        rw [sturmRealDomainRepresentative_spec lam hlam x,
            sturmRealDomainRepresentative_spec lam hlam y]
      _ = sturmRealPolynomialLp lam hlam (p + q) :=
        (sturmRealPolynomialLp_add lam hlam p q).symm
  apply Subtype.ext
  change sturmRealPolynomialLp lam hlam (sturmPolynomial lam r) =
    sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) +
      sturmRealPolynomialLp lam hlam (sturmPolynomial lam q)
  calc
    sturmRealPolynomialLp lam hlam (sturmPolynomial lam r) =
        sturmRealPolynomialLp lam hlam (sturmPolynomial lam (p + q)) :=
      sturmRealPolynomialLp_action_well_defined lam hlam r (p + q) hr
    _ = sturmRealPolynomialLp lam hlam
          (sturmPolynomial lam p + sturmPolynomial lam q) := by
      rw [sturmPolynomial_add]
    _ = sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) +
          sturmRealPolynomialLp lam hlam (sturmPolynomial lam q) :=
      sturmRealPolynomialLp_add lam hlam
        (sturmPolynomial lam p) (sturmPolynomial lam q)

/-- Homogeneity of the actual weighted-L² Sturm polynomial-domain
action for each real scalar. -/
theorem sturmRealDomainOperator_smul
    (lam : ℝ) (hlam : 0 < lam)
    (c : ℝ) (x : sturmRealPolynomialDomain lam hlam) :
    sturmRealDomainOperator lam hlam (c • x) =
      c • sturmRealDomainOperator lam hlam x := by
  let p := sturmRealDomainRepresentative lam hlam x
  let r := sturmRealDomainRepresentative lam hlam (c • x)
  have hr :
      sturmRealPolynomialLp lam hlam r =
        sturmRealPolynomialLp lam hlam (c • p) := by
    calc
      sturmRealPolynomialLp lam hlam r =
          ((c • x : sturmRealPolynomialDomain lam hlam) :
            Lp ℝ 2 (measure lam)) :=
        sturmRealDomainRepresentative_spec lam hlam (c • x)
      _ = c • (x : Lp ℝ 2 (measure lam)) := rfl
      _ = c • sturmRealPolynomialLp lam hlam p := by
        rw [sturmRealDomainRepresentative_spec lam hlam x]
      _ = sturmRealPolynomialLp lam hlam (c • p) :=
        (sturmRealPolynomialLp_smul lam hlam c p).symm
  apply Subtype.ext
  change sturmRealPolynomialLp lam hlam (sturmPolynomial lam r) =
    c • sturmRealPolynomialLp lam hlam (sturmPolynomial lam p)
  calc
    sturmRealPolynomialLp lam hlam (sturmPolynomial lam r) =
        sturmRealPolynomialLp lam hlam (sturmPolynomial lam (c • p)) :=
      sturmRealPolynomialLp_action_well_defined lam hlam r (c • p) hr
    _ = sturmRealPolynomialLp lam hlam
          (c • sturmPolynomial lam p) := by
      rw [sturmPolynomial_smul]
    _ = c • sturmRealPolynomialLp lam hlam (sturmPolynomial lam p) :=
      sturmRealPolynomialLp_smul lam hlam c (sturmPolynomial lam p)

/-- Genuine real-linear unbounded-domain Sturm expression on the
actual weighted L² polynomial-image submodule. This is a linear map,
not a continuous/bounded linear map and not a self-adjoint extension. -/
noncomputable def sturmRealDomainLinear
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPolynomialDomain lam hlam →ₗ[ℝ]
      sturmRealPolynomialDomain lam hlam where
  toFun := sturmRealDomainOperator lam hlam
  map_add' := sturmRealDomainOperator_add lam hlam
  map_smul' := sturmRealDomainOperator_smul lam hlam

theorem sturmRealDomainLinear_symmetric
    (lam : ℝ) (hlam : 0 < lam)
    (x y : sturmRealPolynomialDomain lam hlam) :
    inner ℝ
        ((sturmRealDomainLinear lam hlam x :
          sturmRealPolynomialDomain lam hlam) : Lp ℝ 2 (measure lam))
        (y : Lp ℝ 2 (measure lam)) =
      inner ℝ (x : Lp ℝ 2 (measure lam))
        ((sturmRealDomainLinear lam hlam y :
          sturmRealPolynomialDomain lam hlam) : Lp ℝ 2 (measure lam)) :=
  sturmRealDomainOperator_symmetric lam hlam x y

#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainOperator_add
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainOperator_smul
#print axioms GegenbauerFock.Ultraspherical.sturmRealDomainLinear_symmetric

end GegenbauerFock.Ultraspherical
