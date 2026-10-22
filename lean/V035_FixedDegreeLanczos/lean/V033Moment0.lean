import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_0 : pzero (psub
  (pscale (occupancyScale 0) (scaledMoments[0]?.getD []))
  (clearedOccupancyMoment momentDenominator 0)) = true := by decide
theorem moment_polynomial_0 (M : ℝ) :
 peval (pscale (occupancyScale 0) (scaledMoments[0]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 0) M :=
 checked_equality _ _ moment_cert_0 M
#print axioms moment_cert_0
#print axioms moment_polynomial_0
end V033
