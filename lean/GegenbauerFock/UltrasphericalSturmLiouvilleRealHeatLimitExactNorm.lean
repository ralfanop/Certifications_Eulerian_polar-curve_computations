import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitFirstModes

/-!
# V007 — sharp full-space norm of the Gegenbauer heat-limit semigroup

The genuine real weighted-L2 heat-limit operator is a contraction.
The normalized constant Gegenbauer mode is fixed, so its operator norm
attains the contraction bound at every nonnegative time.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory
private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- Exact full-L2 operator norm of the genuine strongly constructed heat limit. -/
theorem sturmRealHeatLimitCLM_norm_eq_one
    (lam : ℝ) (hlam : 0 < lam) (s : ℝ) (hs : 0 ≤ s) :
    ‖sturmRealHeatLimitCLM lam hlam s hs‖ = 1 := by
  apply le_antisymm (sturmRealHeatLimitCLM_opNorm_le lam hlam s hs)
  let u : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam 0
  have hu : ‖u‖ = 1 :=
    sturmMonicEigenCandidate_realL2_normalized_norm lam hlam 0
  have hfix :
      sturmRealHeatLimitCLM lam hlam s hs u = u :=
    sturmRealHeatLimitCLM_fixed_constant_mode lam hlam s hs
  have hle :
      ‖sturmRealHeatLimitCLM lam hlam s hs u‖ ≤
        ‖sturmRealHeatLimitCLM lam hlam s hs‖ * ‖u‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [hfix, hu, mul_one] at hle
  exact hle

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_norm_eq_one

end GegenbauerFock.Ultraspherical
