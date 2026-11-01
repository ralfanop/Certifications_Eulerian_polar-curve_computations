import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosureSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# V007 — maximal symmetry of the genuine canonical Sturm closure

The actual ultraspherical polynomial Sturm operator's canonical
closure is self-adjoint for every lambda > 0. This upgrades that
result to operator-theoretic maximality: no strictly larger symmetric
partially defined real-linear operator on the genuine L² Hilbert
space can extend the closed differential expression.

The argument uses Mathlib's unbounded adjoint and the exact
formal-adjoint Galois comparison; no complete eigenbasis is assumed.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- There is no proper symmetric extension of the actual self-adjoint
canonical closure of the ultraspherical real Sturm operator. -/
theorem sturmRealClosed_maximal_symmetric
    (lam : ℝ) (hlam : 0 < lam)
    (B : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hAB : (sturmRealPartialOperator lam hlam).closure ≤ B)
    (hBsym : B.IsFormalAdjoint B) :
    B = (sturmRealPartialOperator lam hlam).closure := by
  let A := (sturmRealPartialOperator lam hlam).closure
  have hAself : IsSelfAdjoint A :=
    sturmRealPartialOperator_closure_isSelfAdjoint lam hlam
  have hformal : A.IsFormalAdjoint B := by
    intro x y
    let xB : B.domain := ⟨(x : SturmH lam), hAB.1 x.property⟩
    have hmap : A x = B xB := hAB.2 rfl
    rw [hmap]
    exact hBsym xB y
  have hB_le : B ≤ A.adjoint :=
    hformal.le_adjoint hAself.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hAself] at hB_le
  exact le_antisymm hB_le hAB

/-- Every self-adjoint extension of the genuine canonical closed Sturm
operator is equal to it: the closure is already maximal self-adjoint. -/
theorem sturmRealClosed_unique_selfAdjoint_extension
    (lam : ℝ) (hlam : 0 < lam)
    (B : SturmH lam →ₗ.[ℝ] SturmH lam)
    (hAB : (sturmRealPartialOperator lam hlam).closure ≤ B)
    (hBself : IsSelfAdjoint B) :
    B = (sturmRealPartialOperator lam hlam).closure := by
  have hBformal : B.IsFormalAdjoint B := by
    have h : B.adjoint.IsFormalAdjoint B :=
      LinearPMap.adjoint_isFormalAdjoint hBself.dense_domain
    rw [LinearPMap.isSelfAdjoint_def.mp hBself] at h
    exact h
  exact sturmRealClosed_maximal_symmetric lam hlam B hAB hBformal

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_maximal_symmetric
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_unique_selfAdjoint_extension

end GegenbauerFock.Ultraspherical
