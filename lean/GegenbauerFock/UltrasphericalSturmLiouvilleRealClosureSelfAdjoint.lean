import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedFullResolvent
import GegenbauerFock.UltrasphericalSturmLiouvilleRealClosedSymmetry
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# V007 — the genuine polynomial Sturm closure equals its unbounded adjoint

The closed polynomial-core ultraspherical Sturm operator has an actual
surjective positive shift for every t > 0 and is symmetric on its
canonical closed graph. We use the Hilbert adjoint's defining
inner-product relation and the full shifted surjectivity to prove
that its adjoint domain is contained in its actual closure domain.
The reverse inclusion is formal symmetry. No eigenbasis is assumed.

This proves unbounded self-adjointness of the exact graph closure,
not merely of an auxiliary closed extension or bounded resolvent.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual canonical closed Sturm expression is self-adjoint as an
unbounded partially defined real Hilbert operator, for every lambda > 0.
The real resolvent is evaluated at t = 1. -/
theorem sturmRealPartialOperator_closure_isSelfAdjoint
    (lam : ℝ) (hlam : 0 < lam) :
    IsSelfAdjoint (sturmRealPartialOperator lam hlam).closure := by
  classical
  let A := (sturmRealPartialOperator lam hlam).closure
  have hdense : Dense (A.domain : Set (SturmH lam)) := by
    intro z
    change z ∈ closure (A.domain : Set (SturmH lam))
    rw [← Submodule.topologicalClosure_coe]
    change z ∈ (sturmRealPartialOperator lam hlam).closure.domain.topologicalClosure
    rw [sturmRealPartialOperator_closure_dense_domain lam hlam]
    trivial
  have hsym : A.IsFormalAdjoint A := by
    intro u v
    exact sturmRealPartialOperator_closure_symmetric lam hlam u v
  have hle : A ≤ A.adjoint :=
    hsym.le_adjoint hdense
  have hadj : A.adjoint.IsFormalAdjoint A :=
    LinearPMap.adjoint_isFormalAdjoint hdense
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · refine ⟨?_, ?_⟩
    · intro y hy
      let ya : A.adjoint.domain := ⟨y, hy⟩
      obtain ⟨x, hx⟩ :=
        sturmRealClosedPositiveShift_surjective lam 1 hlam one_pos
          (y - A.adjoint ya)
      have hx' : (x : SturmH lam) - A x = y - A.adjoint ya := by
        simpa only [one_smul] using hx
      have hshift_inner (w : A.domain) :
          inner ℝ (y - (x : SturmH lam))
            ((w : SturmH lam) - A w) = 0 := by
        have hform := hadj ya w
        have hsymw := hsym x w
        have hidentity :
            inner ℝ (y - (x : SturmH lam))
              ((w : SturmH lam) - A w) =
            inner ℝ ((y - A.adjoint ya) -
              ((x : SturmH lam) - A x)) (w : SturmH lam) := by
          simp only [inner_sub_left, inner_sub_right]
          rw [← hform, ← hsymw]
          ring
        rw [hidentity, hx']
        exact sub_self _
      have hyx : y = (x : SturmH lam) := by
        apply ext_inner_right ℝ
        intro z
        obtain ⟨w, hw⟩ :=
          sturmRealClosedPositiveShift_surjective lam 1 hlam one_pos z
        have hw' : (w : SturmH lam) - A w = z := by
          simpa only [one_smul] using hw
        have h := hshift_inner w
        rw [← hw']
        exact sub_eq_zero.mp (by
          simpa only [inner_sub_left] using h)
      rw [hyx]
      exact x.property
  · exact hle


#print axioms GegenbauerFock.Ultraspherical.sturmRealPartialOperator_closure_isSelfAdjoint

end GegenbauerFock.Ultraspherical
