import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_6 : pzero (psub
  (pscale (occupancyScale 6) (scaledMoments[12]?.getD []))
  (clearedOccupancyMoment momentDenominator 6)) = true := by decide
theorem moment_polynomial_6 (M : ℝ) :
 peval (pscale (occupancyScale 6) (scaledMoments[12]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 6) M :=
 checked_equality _ _ moment_cert_6 M
#print axioms moment_cert_6
#print axioms moment_polynomial_6
end V033
