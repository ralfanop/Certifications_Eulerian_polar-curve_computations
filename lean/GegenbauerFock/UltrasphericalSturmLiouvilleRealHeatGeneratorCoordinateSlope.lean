import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitHilbertCoordinates
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatModeDerivative
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarSlope

/-!
# V007 — full-L2 heat difference quotients, one Fourier coordinate at a time

For an arbitrary vector in the actual weighted real L2 space, the n-th
Gegenbauer Fourier coordinate of the right heat difference quotient
converges to -n(n+2lambda) times the initial coordinate.

This is not yet norm convergence of the entire quotient in L2. It is the
coordinate-continuity input for the converse generator-domain inclusion.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Every real weighted-L2 input has the correct right-generator
limit in each individual Hilbert-basis Fourier coordinate. -/
theorem sturmRealHeatLimit_fullL2_coordinate_right_slope
    (lam : ℝ) (hlam : 0 < lam) (f : SturmH lam) (n : ℕ) :
    Tendsto
      (fun s : ℝ =>
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr
          (s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f)) n)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) *
        (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f n)) := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let c : ℝ := (b.repr f) n
  have hscalar :
      Tendsto (fun s : ℝ => (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c)
        (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) * c)) :=
    (sturmRealHeat_scalar_slope_zero_right omega).mul_const c
  have hdiag (s : ℝ) (hs : 0 < s) :
      (b.repr (sturmRealHeatLimitNonnegativeExtended lam hlam s f)) n =
        Real.exp (-s * omega) * c := by
    have h := sturmRealHeatLimitCLM_hilbert_repr_diagonal
      lam hlam s hs.le f n
    simpa [b, c, omega, sturmRealHeatLimitNonnegativeExtended,
      max_eq_right hs.le] using h
  have hevent :
      (fun s : ℝ =>
        (b.repr (s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ => (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [map_smul, map_sub]
    change s⁻¹ * ((b.repr
      (sturmRealHeatLimitNonnegativeExtended lam hlam s f)) n - c) =
      (s⁻¹ • (Real.exp (s * (-omega)) - 1)) * c
    rw [hdiag s hs]
    simp only [smul_eq_mul]
    ring
  change Tendsto
    (fun s : ℝ =>
      (b.repr (s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s f - f))) n)
    (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) * c))
  exact hscalar.congr' hevent.symm

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_fullL2_coordinate_right_slope

end GegenbauerFock.Ultraspherical
