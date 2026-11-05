import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# V007 — right derivative of the Gegenbauer heat scalar multiplier

For any nonnegative Gegenbauer frequency omega, the exact scalar
heat multiplier exp(-s*omega) has right difference quotient tending
to -omega as s decreases to zero. This is an analytic ingredient
of the identification of the full L2 heat semigroup generator.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open Filter
open scoped Topology

/-- At time zero, the exponential spectral multiplier has right
derivative -omega, expressed as a filter limit of difference quotients. -/
theorem sturmRealHeat_scalar_slope_zero_right (omega : ℝ) :
    Tendsto
      (fun s : ℝ => s⁻¹ • (Real.exp (s * (-omega)) - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (-omega)) := by
  have hlinear :
      HasDerivAt (fun s : ℝ => s * (-omega)) (-omega) (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (-omega)
  have hexp :
      HasDerivAt (fun s : ℝ => Real.exp (s * (-omega)))
        (-omega) (0 : ℝ) := by
    simpa using hlinear.exp
  simpa only [zero_add, zero_mul, Real.exp_zero] using
    hexp.tendsto_slope_zero_right

#print axioms GegenbauerFock.Ultraspherical.sturmRealHeat_scalar_slope_zero_right

end GegenbauerFock.Ultraspherical
