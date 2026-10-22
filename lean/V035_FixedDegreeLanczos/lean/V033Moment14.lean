import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_14 : pzero (psub
  (pscale (occupancyScale 14) (scaledMoments[28]?.getD []))
  (clearedOccupancyMoment momentDenominator 14)) = true := by decide
theorem moment_polynomial_14 (M : ℝ) :
 peval (pscale (occupancyScale 14) (scaledMoments[28]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 14) M :=
 checked_equality _ _ moment_cert_14 M
#print axioms moment_cert_14
#print axioms moment_polynomial_14
end V033
