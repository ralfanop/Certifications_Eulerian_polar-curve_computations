import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_1 : pzero (psub
  (pscale (occupancyScale 1) (scaledMoments[2]?.getD []))
  (clearedOccupancyMoment momentDenominator 1)) = true := by decide
theorem moment_polynomial_1 (M : ℝ) :
 peval (pscale (occupancyScale 1) (scaledMoments[2]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 1) M :=
 checked_equality _ _ moment_cert_1 M
#print axioms moment_cert_1
#print axioms moment_polynomial_1
end V033
