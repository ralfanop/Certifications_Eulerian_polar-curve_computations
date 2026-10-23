import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_2 : pzero (psub
  (pscale (occupancyScale 2) (scaledMoments[4]?.getD []))
  (clearedOccupancyMoment momentDenominator 2)) = true := by decide
theorem moment_polynomial_2 (M : ℝ) :
 peval (pscale (occupancyScale 2) (scaledMoments[4]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 2) M :=
 checked_equality _ _ moment_cert_2 M
#print axioms moment_cert_2
#print axioms moment_polynomial_2
end V033
