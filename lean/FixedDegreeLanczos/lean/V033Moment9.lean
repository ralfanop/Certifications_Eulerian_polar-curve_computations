import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_9 : pzero (psub
  (pscale (occupancyScale 9) (scaledMoments[18]?.getD []))
  (clearedOccupancyMoment momentDenominator 9)) = true := by decide
theorem moment_polynomial_9 (M : ℝ) :
 peval (pscale (occupancyScale 9) (scaledMoments[18]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 9) M :=
 checked_equality _ _ moment_cert_9 M
#print axioms moment_cert_9
#print axioms moment_polynomial_9
end V033
