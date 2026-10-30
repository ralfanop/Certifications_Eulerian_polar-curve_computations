import GegenbauerFock.UltrasphericalSturmLiouvilleRealGraphClosureCore

/-!
# V007 — dense domain and exact graph core of the canonical closed operator

The actual dense symmetric real Sturm operator on weighted L² has a
certified closed graph closure. Because the original domain is dense
and is contained in the closure domain, the canonical closed extension
also has dense domain. The original polynomial domain remains its
certified graph core.

This does not imply self-adjointness of the closure.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

theorem sturmRealClosedPMap_domain_dense
    (lam : ℝ) (hlam : 0 < lam) :
    Dense ((sturmRealPMap lam hlam).closure.domain :
      Set (Lp ℝ 2 (measure lam))) := by
  intro x
  have h0 :
      x ∈ closure ((sturmRealPMap lam hlam).domain :
        Set (Lp ℝ 2 (measure lam))) :=
    sturmRealPMap_domain_dense lam hlam x
  have hle :
      (sturmRealPMap lam hlam).domain ≤
        (sturmRealPMap lam hlam).closure.domain :=
    LinearPMap.domain_mono (LinearPMap.le_closure (sturmRealPMap lam hlam))
  exact closure_mono (show
    ((sturmRealPMap lam hlam).domain :
      Set (Lp ℝ 2 (measure lam))) ⊆
    ((sturmRealPMap lam hlam).closure.domain :
      Set (Lp ℝ 2 (measure lam))) from hle) h0

/-- The canonical closed real ultraspherical Sturm extension is both
closed and densely defined on the genuine weighted Hilbert space. -/
theorem sturmRealClosedPMap_closed_and_dense
    (lam : ℝ) (hlam : 0 < lam) :
    (sturmRealPMap lam hlam).closure.IsClosed ∧
    Dense ((sturmRealPMap lam hlam).closure.domain :
      Set (Lp ℝ 2 (measure lam))) :=
  ⟨sturmRealPMap_closure_isClosed lam hlam,
    sturmRealClosedPMap_domain_dense lam hlam⟩

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedPMap_domain_dense
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedPMap_closed_and_dense

end GegenbauerFock.Ultraspherical
