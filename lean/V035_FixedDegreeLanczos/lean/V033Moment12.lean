import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_12 : pzero (psub
  (pscale (occupancyScale 12) (scaledMoments[24]?.getD []))
  (clearedOccupancyMoment momentDenominator 12)) = true := by decide
theorem moment_polynomial_12 (M : ℝ) :
 peval (pscale (occupancyScale 12) (scaledMoments[24]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 12) M :=
 checked_equality _ _ moment_cert_12 M
#print axioms moment_cert_12
#print axioms moment_polynomial_12
end V033
