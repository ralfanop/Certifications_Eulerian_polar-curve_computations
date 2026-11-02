import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatLimitCLM
import GegenbauerFock.UltrasphericalSturmLiouvilleRealYosidaExponentialModeLimit

/-!
# V007 — exact action of the full-L² heat-limit operator on each Gegenbauer mode

The genuine heat-limit continuous linear map H_s is the strong limit
of the bounded Yosida exponentials on every actual weighted-real-L²
vector. Each normalized Gegenbauer mode already has a separately
kernel-certified spectral exponential limit.

Uniqueness of limits identifies the H_s eigenvalue explicitly, with
NO assumption about an unbounded heat-semigroup generator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The actual full-L² contractive limiting heat operator acts diagonally
on every genuinely normalized real Gegenbauer eigenmode. -/
theorem sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen
    (lam : ℝ) (hlam : 0 < lam)
    (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    sturmRealHeatLimitCLM lam hlam s hs
      (sturmMonicEigenCandidate_realL2_normalized lam hlam n) =
      (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n := by
  let v : SturmH lam :=
    sturmMonicEigenCandidate_realL2_normalized lam hlam n
  have hfull :
      Tendsto
        (fun k : ℕ => sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s v)
        atTop (𝓝 (sturmRealHeatLimitVector lam hlam s hs v)) :=
    sturmRealHeatLimitVector_tendsto lam hlam s hs v
  have hmode :
      Tendsto
        (fun k : ℕ => sturmRealYosidaExponential lam ((k : ℝ) + 1) hlam
          (by positivity : 0 < (k : ℝ) + 1) s v)
        atTop
        (𝓝 ((Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) • v)) :=
    sturmRealYosidaExponential_Gegenbauer_mode_tendsto lam hlam n s
  have heq := tendsto_nhds_unique hfull hmode
  change sturmRealHeatLimitVector lam hlam s hs v =
    (Real.exp (-s * ((n : ℝ) * ((n : ℝ) + 2 * lam)))) • v
  exact heq

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimitCLM_normalized_Gegenbauer_eigen

end GegenbauerFock.Ultraspherical
