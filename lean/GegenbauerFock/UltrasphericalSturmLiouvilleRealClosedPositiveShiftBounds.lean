import GegenbauerFock.UltrasphericalSturmLiouvilleRealEnergyNonpositive
import GegenbauerFock.UltrasphericalSturmLiouvilleRealPositiveShiftDenseRange
import GegenbauerFock.UltrasphericalSturmLiouvillePositiveShiftNormBound

/-!
# V007 — actual closed Sturm: quantitative positive shifts and dense ranges

The true weighted-real-L² canonical graph closure now has a
kernel-certified nonpositive quadratic form, not an assumed one.

Apply the already certified sharp estimate for every t>0,
show that its positive shift has trivial kernel, and transport the
certified dense range from the original polynomial graph into the
canonical closed graph.

This is a direct result about the real closed operator itself.
It does not yet assert surjectivity of the closed shifted range.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical
open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Sharp quantitative shift bound for the ACTUAL canonical closed
ultraspherical differential operator in real weighted L². -/
theorem sturmRealClosedPositiveShift_norm
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain) :
    t * ‖(x : SturmH lam)‖ ≤
      ‖t • (x : SturmH lam) -
        (sturmRealPartialOperator lam hlam).closure x‖ :=
  sturmReal_nonpositive_positive_shift_norm lam t ht
    (sturmRealPartialOperator lam hlam).closure
    (sturmRealPartialOperator_closure_nonpositive lam hlam) x

/-- No nonzero vector in the actual full closed domain satisfies
(tI - Abar)x=0, for ANY t>0. -/
theorem sturmRealClosedPositiveShift_kernel
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t)
    (x : (sturmRealPartialOperator lam hlam).closure.domain)
    (hx : t • (x : SturmH lam) -
      (sturmRealPartialOperator lam hlam).closure x = 0) :
    x = 0 :=
  sturmReal_nonpositive_positive_shift_kernel lam t ht
    (sturmRealPartialOperator lam hlam).closure
    (sturmRealPartialOperator_closure_nonpositive lam hlam) x hx

/-- The true closed real weighted-L² Sturm operator has dense
positive-shifted range for EVERY real t>0. This uses certified
polynomial preimages plus inclusion of the original graph in
the canonical closed graph. -/
theorem sturmRealClosedPositiveShift_denseRange
    (lam t : ℝ) (hlam : 0 < lam) (ht : 0 < t) :
    DenseRange
      (fun y : (sturmRealPartialOperator lam hlam).closure.domain =>
        t • (y : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure y) := by
  let A := sturmRealPartialOperator lam hlam
  have hsmall :
      DenseRange (fun x : A.domain =>
        t • (x : SturmH lam) - A x) :=
    sturmRealPartialPositiveShift_denseRange lam t hlam ht
  have hsub :
      Set.range (fun x : A.domain =>
          t • (x : SturmH lam) - A x) ⊆
        Set.range (fun y : A.closure.domain =>
          t • (y : SturmH lam) - A.closure y) := by
    rintro z ⟨x, rfl⟩
    obtain ⟨v, hv, hAv⟩ :=
      LinearPMap.exists_of_le
        (sturmRealPartialOperator_le_closed_extension lam hlam) x
    refine ⟨v, ?_⟩
    change t • (v : SturmH lam) - A.closure v =
      t • (x : SturmH lam) - A x
    rw [hv, hAv]
  exact hsmall.mono hsub

/-- Quantitative graph control at t=1 now holds for the concrete
canonical closed ultraspherical real Sturm operator itself. -/
theorem sturmRealClosed_shift_graph_bound
    (lam : ℝ) (hlam : 0 < lam)
    (x y : (sturmRealPartialOperator lam hlam).closure.domain) :
    dist (((x : SturmH lam),
        (sturmRealPartialOperator lam hlam).closure x) :
          SturmH lam × SturmH lam)
      (((y : SturmH lam),
        (sturmRealPartialOperator lam hlam).closure y) :
          SturmH lam × SturmH lam) ≤
      3 * dist ((x : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure x)
        ((y : SturmH lam) -
          (sturmRealPartialOperator lam hlam).closure y) :=
  sturmReal_closed_nonpositive_shift_graph_bound lam
    (sturmRealPartialOperator lam hlam).closure
    (sturmRealPartialOperator_closure_nonpositive lam hlam) x y

#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedPositiveShift_norm
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedPositiveShift_kernel
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosedPositiveShift_denseRange
#print axioms GegenbauerFock.Ultraspherical.sturmRealClosed_shift_graph_bound

end GegenbauerFock.Ultraspherical
