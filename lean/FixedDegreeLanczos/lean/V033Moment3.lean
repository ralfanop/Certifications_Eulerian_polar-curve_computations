import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_3 : pzero (psub
  (pscale (occupancyScale 3) (scaledMoments[6]?.getD []))
  (clearedOccupancyMoment momentDenominator 3)) = true := by decide
theorem moment_polynomial_3 (M : ℝ) :
 peval (pscale (occupancyScale 3) (scaledMoments[6]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 3) M :=
 checked_equality _ _ moment_cert_3 M
#print axioms moment_cert_3
#print axioms moment_polynomial_3
end V033
