import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_4 : pzero (psub
  (pscale (occupancyScale 4) (scaledMoments[8]?.getD []))
  (clearedOccupancyMoment momentDenominator 4)) = true := by decide
theorem moment_polynomial_4 (M : ℝ) :
 peval (pscale (occupancyScale 4) (scaledMoments[8]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 4) M :=
 checked_equality _ _ moment_cert_4 M
#print axioms moment_cert_4
#print axioms moment_polynomial_4
end V033
