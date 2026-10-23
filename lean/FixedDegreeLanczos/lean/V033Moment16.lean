import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_16 : pzero (psub
  (pscale (occupancyScale 16) (scaledMoments[32]?.getD []))
  (clearedOccupancyMoment momentDenominator 16)) = true := by decide
theorem moment_polynomial_16 (M : ℝ) :
 peval (pscale (occupancyScale 16) (scaledMoments[32]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 16) M :=
 checked_equality _ _ moment_cert_16 M
#print axioms moment_cert_16
#print axioms moment_polynomial_16
end V033
