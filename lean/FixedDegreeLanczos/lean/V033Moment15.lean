import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_15 : pzero (psub
  (pscale (occupancyScale 15) (scaledMoments[30]?.getD []))
  (clearedOccupancyMoment momentDenominator 15)) = true := by decide
theorem moment_polynomial_15 (M : ℝ) :
 peval (pscale (occupancyScale 15) (scaledMoments[30]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 15) M :=
 checked_equality _ _ moment_cert_15 M
#print axioms moment_cert_15
#print axioms moment_polynomial_15
end V033
