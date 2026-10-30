import GegenbauerFock.UltrasphericalSturmLiouvilleRealDomainLinear
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialDensity
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# V007 — genuinely densely-defined real ultraspherical Sturm LinearPMap

The polynomial-image action on the actual Hilbert space L²(νλ; ℝ)
is represented by Mathlib's partially defined linear operator API,
with exactly its true polynomial image as domain. This imports the
previously proved linearity, genuine Green symmetry and density.

This is NOT a closedness, closability or self-adjointness assertion.
The graph-closure/deficiency analysis is the next independent step.
-/

noncomputable section

namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The genuine polynomial Sturm expression as a partial, potentially
unbounded linear operator on the entire weighted real L² Hilbert space. -/
noncomputable def sturmRealPartialOperator
    (lam : ℝ) (hlam : 0 < lam) :
    Lp ℝ 2 (measure lam) →ₗ.[ℝ] Lp ℝ 2 (measure lam) where
  domain := sturmRealPolynomialDomain lam hlam
  toFun := (sturmRealPolynomialDomain lam hlam).subtype.comp
    (sturmRealDomainLinear lam hlam)

/-- Its domain is exactly the concrete polynomial-image submodule. -/
theorem sturmRealPartialOperator_domain
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).domain =
      sturmRealPolynomialDomain lam hlam := rfl

/-- The partial operator acts by the representative-independent
Sturm differential expression on every polynomial-image vector. -/
theorem sturmRealPartialOperator_apply
    (lam : ℝ) (hlam : 0 < lam)
    (x : sturmRealPolynomialDomain lam hlam) :
    sturmRealPartialOperator lam hlam x =
      ((sturmRealDomainLinear lam hlam x :
        sturmRealPolynomialDomain lam hlam) :
          Lp ℝ 2 (measure lam)) := rfl

/-- The genuine Green identity, now formulated on a Mathlib
partially defined unbounded operator. -/
theorem sturmRealPartialOperator_symmetric
    (lam : ℝ) (hlam : 0 < lam)
    (x y : sturmRealPolynomialDomain lam hlam) :
    inner ℝ (sturmRealPartialOperator lam hlam x)
      (y : Lp ℝ 2 (measure lam)) =
    inner ℝ (x : Lp ℝ 2 (measure lam))
      (sturmRealPartialOperator lam hlam y) := by
  change inner ℝ
      ((sturmRealDomainLinear lam hlam x :
          sturmRealPolynomialDomain lam hlam) :
        Lp ℝ 2 (measure lam))
      (y : Lp ℝ 2 (measure lam)) =
    inner ℝ (x : Lp ℝ 2 (measure lam))
      ((sturmRealDomainLinear lam hlam y :
          sturmRealPolynomialDomain lam hlam) :
        Lp ℝ 2 (measure lam))
  exact sturmRealDomainLinear_symmetric lam hlam x y

/-- Density of the EXACT domain of the partial operator in the
entire real weighted Hilbert space. -/
theorem sturmRealPartialOperator_dense_domain
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPartialOperator lam hlam).domain.topologicalClosure =
      ⊤ := by
  change (sturmRealPolynomialDomain lam hlam).topologicalClosure = ⊤
  exact sturmRealPolynomialDomain_dense lam hlam

#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_domain
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_apply
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_symmetric
#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_dense_domain

end GegenbauerFock.Ultraspherical
