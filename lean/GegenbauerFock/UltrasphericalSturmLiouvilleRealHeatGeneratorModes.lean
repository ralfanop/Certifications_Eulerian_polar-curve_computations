import GegenbauerFock.UltrasphericalSturmLiouvilleRealHeatModeDerivative

/-!
# V007 — infinitesimal generator on normalized Gegenbauer eigenmodes

Compatibility theorem using the independently proved and kernel-audited
scalar difference-quotient and genuine L² heat-mode derivative result.
This module deliberately does not duplicate analytic differentiation
arguments or assume the complete generator-domain identity.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open MeasureTheory Filter
open scoped Topology

private abbrev SturmH (lam : ℝ) := Lp ℝ 2 (measure lam)

/-- The full-L² heat contraction semigroup has the exact infinitesimal
right derivative on every normalized Gegenbauer mode. -/
theorem sturmRealHeatLimit_generator_on_normalized_Gegenbauer
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Tendsto
      (fun h : ℝ => h⁻¹ •
        (sturmRealHeatLimitNonnegativeExtended lam hlam h
          (sturmMonicEigenCandidate_realL2_normalized lam hlam n) -
         sturmMonicEigenCandidate_realL2_normalized lam hlam n))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((-((n : ℝ) * ((n : ℝ) + 2 * lam))) •
        sturmMonicEigenCandidate_realL2_normalized lam hlam n)) := by
  exact sturmRealHeatLimit_mode_right_slope lam hlam n

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeatLimit_generator_on_normalized_Gegenbauer

end GegenbauerFock.Ultraspherical
