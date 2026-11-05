import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatGeneratorCoordinateSlope
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarSlope
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitModeContinuity
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — necessary spectral-coordinate condition for the heat generator domain

Suppose the right time-zero difference quotient of the *actual* strongly
continuous weighted-real-L² heat semigroup converges in L² to g. Then each
Gegenbauer Fourier coordinate of g equals the closed Sturm spectral
multiplier of the corresponding coordinate of f.

Unlike a statement only about polynomial eigenmodes, this theorem is
quantified over arbitrary f and g in the full weighted L² and makes
no a priori closed-operator-domain assumption. Together with Parseval
and the certified exact closed Sturm spectral domain, it provides the
reverse domain inclusion required to identify the generator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Any actual strong right derivative of the heat orbit has exactly
the canonical Gegenbauer Sturm Fourier coordinates at every degree. -/
theorem sturmRealHeatLimit_right_derivative_repr
    (lam : ℝ) (hlam : 0 < lam) (f g : SturmH lam)
    (hderiv : Tendsto
      (fun s : ℝ =>
        s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))
      (𝓝[>] (0 : ℝ)) (𝓝 g))
    (n : ℕ) :
    (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g n =
      (-((n : ℝ) * ((n : ℝ) + 2 * lam))) *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hlimit :
      Tendsto
        (fun s : ℝ =>
          (b.repr (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
        (𝓝[>] (0 : ℝ)) (𝓝 ((b.repr g) n)) := by
    have h := ((innerSL ℝ (b n)).continuous.tendsto g).comp hderiv
    have h' :
        Tendsto
          (fun t : ℝ => inner ℝ (b n)
            (t⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam t f - f)))
          (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ (b n) g)) := by
      simpa only [Function.comp_def, innerSL_apply_apply] using h
    simpa only [← HilbertBasis.repr_apply_apply] using h'
  have hcoordinate :=
    sturmRealHeatLimit_fullL2_coordinate_right_slope lam hlam f n
  have hunique := tendsto_nhds_unique hlimit hcoordinate
  exact hunique

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_right_derivative_repr

end GegenbauerFock.Ultraspherical
