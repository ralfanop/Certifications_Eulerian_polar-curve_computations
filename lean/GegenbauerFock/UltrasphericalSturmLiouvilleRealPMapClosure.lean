import GegenbauerFock.UltrasphericalSturmLiouvilleRealDomainLinear
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPolynomialDensity
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# V007 — actual densely-defined ultraspherical real Sturm operator and closure

The genuine real weighted-L² polynomial-domain operator already
Lean-certified as symmetric and linear is expressed as Mathlib's
partially defined linear map (LinearPMap) on the ambient Hilbert space.

The certified Weierstrass approximation yields a dense actual domain.
The Hilbert-space adjoint is closed; symmetry embeds our operator in
its closed adjoint, hence it is closable.

This does NOT assert self-adjointness or essential self-adjointness.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The actual partially defined linear differential operator on
the real Hilbert L² of the genuine Beta-pushforward law. -/
noncomputable def sturmRealPMap
    (lam : ℝ) (hlam : 0 < lam) :
    (Lp ℝ 2 (measure lam)) →ₗ.[ℝ] (Lp ℝ 2 (measure lam)) where
  domain := sturmRealPolynomialDomain lam hlam
  toFun := (sturmRealPolynomialDomain lam hlam).subtype.comp
    (sturmRealDomainLinear lam hlam)

/-- The concrete real polynomial domain of the genuine PMap is dense. -/
theorem sturmRealPMap_domain_dense
    (lam : ℝ) (hlam : 0 < lam) :
    Dense ((sturmRealPMap lam hlam).domain :
      Set (Lp ℝ 2 (measure lam))) := by
  change Dense (sturmRealPolynomialDomain lam hlam :
    Set (Lp ℝ 2 (measure lam)))
  intro x
  have hx :
      x ∈ (sturmRealPolynomialDomain lam hlam).topologicalClosure := by
    rw [sturmRealPolynomialDomain_dense lam hlam]
    trivial
  exact hx

/-- The operator is formally symmetric on its dense real L² core. -/
theorem sturmRealPMap_formalSymmetric
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).IsFormalAdjoint
      (sturmRealPMap lam hlam) := by
  intro x y
  exact sturmRealDomainLinear_symmetric lam hlam x y

/-- A densely defined symmetric real Hilbert operator is closable,
applied to the genuine ultraspherical Sturm polynomial core. -/
theorem sturmRealPMap_isClosable
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).IsClosable := by
  have hdense := sturmRealPMap_domain_dense lam hlam
  have hformal := sturmRealPMap_formalSymmetric lam hlam
  have hle :
      sturmRealPMap lam hlam ≤
        (sturmRealPMap lam hlam).adjoint :=
    hformal.le_adjoint hdense
  have hclosed :
      (sturmRealPMap lam hlam).adjoint.IsClosed :=
    LinearPMap.adjoint_isClosed hdense
  exact hclosed.isClosable.leIsClosable hle

/-- The canonical graph closure is a closed extension of the genuine
densely-defined polynomial Sturm operator in real weighted L². -/
theorem sturmRealPMap_closure_isClosed
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).closure.IsClosed :=
  (sturmRealPMap_isClosable lam hlam).closure_isClosed

theorem sturmRealPMap_le_closure
    (lam : ℝ) (hlam : 0 < lam) :
    sturmRealPMap lam hlam ≤ (sturmRealPMap lam hlam).closure :=
  LinearPMap.le_closure _

#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_domain_dense
#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_formalSymmetric
#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_isClosable
#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_closure_isClosed
#print axioms GegenbauerFock.Ultraspherical.sturmRealPMap_le_closure

end GegenbauerFock.Ultraspherical
