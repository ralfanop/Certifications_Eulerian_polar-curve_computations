import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarSlope
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
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let c : ℝ := (b.repr f) n
  have hlimit :
      Tendsto
        (fun s : ℝ =>
          (b.repr (s⁻¹ •
            (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
        (𝓝[>] (0 : ℝ)) (𝓝 ((b.repr g) n)) := by
    have hcont : Continuous (fun x : SturmH lam => (b.repr x) n) :=
      (PiLp.continuous_apply 2 (fun _ : ℕ => ℝ) n).comp b.repr.continuous
    exact (hcont.tendsto g).comp hderiv
  have hspectral (s : ℝ) (hs : 0 < s) :
      (b.repr (sturmRealHeatLimitNonnegativeExtended lam hlam s f)) n =
        Real.exp (-s * omega) * c := by
    have h := sturmRealHeatLimitCLM_hilbert_repr_diagonal lam hlam
      (max (0 : ℝ) s) (le_max_left (0 : ℝ) s) f n
    simpa only [max_eq_right hs.le] using h
  have hpoint (s : ℝ) (hs : 0 < s) :
      (b.repr (s⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n =
        (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c := by
    simp only [map_smul, map_sub, smul_eq_mul]
    rw [hspectral s hs]
    dsimp [c]
    ring
  have hevent :
      (fun s : ℝ =>
        (b.repr (s⁻¹ •
          (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ => (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hpoint s hs
  have hscalar :
      Tendsto (fun s : ℝ =>
        (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c)
        (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) * c)) :=
    (sturmRealHeat_scalar_slope_zero_right omega).mul_const c
  have hother := hlimit.congr' hevent
  have heq := tendsto_nhds_unique hother hscalar
  change (b.repr g) n = -omega * c
  exact heq

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_right_derivative_repr

end GegenbauerFock.Ultraspherical
