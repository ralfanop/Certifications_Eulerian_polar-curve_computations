import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatScalarSlope
import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitModeContinuity

/-!
# V007 — right infinitesimal derivative of genuine L2 heat eigenmodes

The true strongly constructed heat-limit continuous linear operator,
extended to all real times by max(0,s), has on each normalized
Gegenbauer mode a right derivative at zero equal to the closed Sturm
eigenvalue action. This does not assert the full L2 generator-domain
identification, which requires the separate spectral summability step.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The genuine L2 heat semigroup has the expected right infinitesimal
derivative on each normalized Gegenbauer eigenvector. -/
theorem sturmRealHeatLimit_mode_right_slope
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Tendsto
      (fun s : ℝ =>
        s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n) -
          sturmMonicEigenCandidate_realL2_normalized lam hlam n))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  let omega : ℝ := (n : ℝ) * ((n : ℝ) + 2 * lam)
  let v : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have hscalar := sturmRealHeat_scalar_slope_zero_right omega
  have hv := hscalar.smul_const v
  have hmode (s : ℝ) (hs : 0 < s) :
      sturmRealHeatLimitNonnegativeExtended lam hlam s v =
        Real.exp (s * (-omega)) • v := by
    have h := sturmRealHeatLimitNonnegativeExtended_mode lam hlam s n
    simpa only [max_eq_right hs.le, neg_mul, mul_neg] using h
  have heq :
      (fun s : ℝ =>
        s⁻¹ • (sturmRealHeatLimitNonnegativeExtended lam hlam s v - v))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun s : ℝ => (s⁻¹ • (Real.exp (s * (-omega)) - 1)) • v) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hmode s hs]
    calc
      s⁻¹ • (Real.exp (s * (-omega)) • v - v) =
          s⁻¹ • ((Real.exp (s * (-omega)) - 1) • v) := by
            rw [sub_smul, one_smul]
      _ = (s⁻¹ • (Real.exp (s * (-omega)) - 1)) • v := by
            rw [smul_smul]
            rfl
  change Tendsto
    (fun s : ℝ => s⁻¹ •
      (sturmRealHeatLimitNonnegativeExtended lam hlam s v - v))
    (𝓝[>] (0 : ℝ)) (𝓝 ((-omega) • v))
  exact hv.congr' heq.symm

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_mode_right_slope

end GegenbauerFock.Ultraspherical
