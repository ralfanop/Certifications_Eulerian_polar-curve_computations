import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitMeanZeroDecay

/-!
# V007 — sharp two-source same-mean L² stability of genuine heat flow

The full weighted-real-L² heat semigroup contracts two initial states
with the same degree-zero Gegenbauer coefficient at the optimal first
spectral-gap rate. The result is genuinely infinite-dimensional and
follows by linearity and the already kernel-certified sharp mean-zero
bound, with no additional finite-mode assumptions.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- If two actual weighted-L² inputs have the same constant Gegenbauer
coefficient, their heat trajectories approach each other at the sharp
spectral-gap exponential rate. -/
theorem sturmRealHeatLimitCLM_same_mean_exponential_stability
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (f g : SturmH lam)
    (hmean :
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr f 0 =
      (sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam).repr g 0) :
    ‖sturmRealHeatLimitCLM lam hlam s hs f -
      sturmRealHeatLimitCLM lam hlam s hs g‖ ≤
      Real.exp (-s * (1 + 2 * lam)) * ‖f - g‖ := by
  let b := sturmMonicEigenCandidate_realL2_hilbertBasis lam hlam
  have hzero : (b.repr (f - g)) 0 = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr hmean
  have hdecay :=
    sturmRealHeatLimitCLM_mean_zero_exponential_decay
      lam hlam s hs (f - g) hzero
  simpa only [map_sub] using hdecay

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_same_mean_exponential_stability

end GegenbauerFock.Ultraspherical
