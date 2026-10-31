import GegenbauerFock.UltrasphericalSturmLiouvilleRealResolventSpectralGraph
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# V007 — self-adjointness of the exact bounded full-L² real Sturm resolvent

The certified closed Sturm spectral-graph theorem gives symmetry of
the genuine all-L² continuous resolvent, for every t > 0.
A bounded Hilbert-space operator is self-adjoint precisely when its
underlying linear map is symmetric. Thus the actual inverse of
tI - closure(A) is a self-adjoint bounded continuous linear map.

This is an unconditional statement about the exact real
ultraspherical Hilbert operator, not a truncated matrix model.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

/-- The full-space positive-shift resolvent of the true closed
ultraspherical Sturm operator is self-adjoint on weighted real L². -/
theorem sturmRealPositiveResolventFullCLM_isSelfAdjoint
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    IsSelfAdjoint (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  exact sturmRealPositiveResolventFullCLM_inner_symmetric
    lam t hlam ht f g


/-- The full real weighted-L² Sturm resolvent has no kernel:
if two right-hand sides have the same resolvent image, the closed graph
forces the right-hand sides themselves to coincide. -/
theorem sturmRealPositiveResolventFullCLM_injective
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    Function.Injective (sturmRealPositiveResolventFullCLM lam t hlam ht) := by
  let A := sturmRealPartialOperator lam hlam
  let R := sturmRealPositiveResolventFullCLM lam t hlam ht
  intro f g hfg
  obtain ⟨x, hx⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht f)
  obtain ⟨y, hy⟩ := (A.closure.mem_graph_iff').mp
    (sturmRealPositiveResolventFullCLM_closed_graph lam t hlam ht g)
  have hx1 : (x : Lp ℝ 2 (measure lam)) = R f :=
    congrArg Prod.fst hx
  have hy1 : (y : Lp ℝ 2 (measure lam)) = R g :=
    congrArg Prod.fst hy
  have hxy : x = y := by
    apply Subtype.ext
    exact hx1.trans (hfg.trans hy1.symm)
  have hx2 : A.closure x = t • R f - f :=
    congrArg Prod.snd hx
  have hy2 : A.closure y = t • R g - g :=
    congrArg Prod.snd hy
  rw [hxy, hfg] at hx2
  have hsame : t • R g - f = t • R g - g :=
    hx2.symm.trans hy2
  apply sub_eq_zero.mp
  calc
    f - g =
        (t • R g - (t • R g - f)) -
          (t • R g - (t • R g - g)) := by abel
    _ = 0 := by rw [hsame]; abel

#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_isSelfAdjoint
#print axioms GegenbauerFock.Ultraspherical.sturmRealPositiveResolventFullCLM_injective

end GegenbauerFock.Ultraspherical
