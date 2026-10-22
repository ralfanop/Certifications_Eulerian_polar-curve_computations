import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_10 : pzero (psub
  (pscale (occupancyScale 10) (scaledMoments[20]?.getD []))
  (clearedOccupancyMoment momentDenominator 10)) = true := by decide
theorem moment_polynomial_10 (M : ℝ) :
 peval (pscale (occupancyScale 10) (scaledMoments[20]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 10) M :=
 checked_equality _ _ moment_cert_10 M
#print axioms moment_cert_10
#print axioms moment_polynomial_10
end V033
