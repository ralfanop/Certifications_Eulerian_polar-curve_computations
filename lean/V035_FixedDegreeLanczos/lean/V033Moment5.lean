import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_5 : pzero (psub
  (pscale (occupancyScale 5) (scaledMoments[10]?.getD []))
  (clearedOccupancyMoment momentDenominator 5)) = true := by decide
theorem moment_polynomial_5 (M : ℝ) :
 peval (pscale (occupancyScale 5) (scaledMoments[10]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 5) M :=
 checked_equality _ _ moment_cert_5 M
#print axioms moment_cert_5
#print axioms moment_polynomial_5
end V033
