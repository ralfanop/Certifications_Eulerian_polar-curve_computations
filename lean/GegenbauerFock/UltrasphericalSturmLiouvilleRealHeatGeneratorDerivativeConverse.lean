import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorGraphBridge
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitModeContinuity
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarSlope
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — converse generator-domain theorem on the actual weighted real L²

If the actual full weighted-L² heat semigroup admits a strong right
derivative g at time zero for input f, then f belongs to the domain
of the CANONICAL polynomial Sturm closure and the closed operator
takes f to g.

No abstract diagonal extension is introduced. The proof takes the
continuous Gegenbauer Hilbert coordinate of the strong derivative,
computes its scalar limit using the exact heat multiplier, and then
applies the separately audited canonical Sturm graph criterion.

The forward implication (existence of a strong derivative on the
entire canonical closed domain) remains a separate proof obligation.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Any strong right-time-zero derivative of the genuine Gegenbauer
heat limit must equal the CANONICAL closed Sturm operator, with the
correct original closed-domain membership. -/
theorem sturmRealHeat_right_derivative_implies_closed_sturm_graph
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam)
    (hderiv : Tendsto
      (fun s : ℝ => s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g)) :
    ∃ x : (sturmRealPartialOperator lam hlam).closure.domain,
      (x : SturmH lam) = f ∧
        (sturmRealPartialOperator lam hlam).closure x = g := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let T := sturmRealHeatLimitNonnegativeExtended lam hlam
  apply sturmRealClosed_graph_of_diagonal_coefficients lam hlam f g
  intro n
  let w : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  have hcoord :
      Tendsto
        (fun s : ℝ => (b.repr (s⁻¹ • (T s f - f))) n)
        (𝓝[>] (0 : ℝ)) (𝓝 ((b.repr g) n)) := by
    have hinner :=
      ((innerSL ℝ (b n)).continuous.tendsto g).comp hderiv
    simpa only [HilbertBasis.repr_apply_apply] using hinner
  have hpoint (s : ℝ) (hs : 0 < s) :
      (b.repr (s⁻¹ • (T s f - f))) n =
        (s⁻¹ • (Real.exp (s * (-w)) - 1)) * (b.repr f) n := by
    have hT :
        (b.repr (T s f)) n =
          Real.exp (-s * w) * (b.repr f) n := by
      change (b.repr
        (sturmRealHeatLimitCLM lam hlam (max (0 : ℝ) s)
          (le_max_left (0 : ℝ) s) f)) n = _
      simpa only [max_eq_right hs.le, w] using
        (sturmRealHeatLimitCLM_hilbert_repr_diagonal
          lam hlam s hs.le f n)
    calc
      (b.repr (s⁻¹ • (T s f - f))) n =
          s⁻¹ * ((b.repr (T s f)) n - (b.repr f) n) := by
            simp only [map_smul, map_sub, smul_eq_mul]
      _ = (s⁻¹ • (Real.exp (s * (-w)) - 1)) *
          (b.repr f) n := by
            rw [hT]
            simp only [smul_eq_mul]
            have harg : s * (-w) = -s * w := by ring
            rw [harg]
            ring
  have hevent :
      (fun s : ℝ => (b.repr (s⁻¹ • (T s f - f))) n) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ =>
        (s⁻¹ • (Real.exp (s * (-w)) - 1)) * (b.repr f) n) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hpoint s hs
  have hscalar :
      Tendsto
        (fun s : ℝ =>
          (s⁻¹ • (Real.exp (s * (-w)) - 1)) * (b.repr f) n)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((-w) * (b.repr f) n)) :=
    (sturmRealHeat_scalar_slope_zero_right w).mul_const ((b.repr f) n)
  have hsame := tendsto_nhds_unique (hcoord.congr' hevent) hscalar
  simpa only [w, neg_mul] using hsame

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_right_derivative_implies_closed_sturm_graph

end GegenbauerFock.Ultraspherical
