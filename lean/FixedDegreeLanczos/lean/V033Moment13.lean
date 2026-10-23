import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_13 : pzero (psub
  (pscale (occupancyScale 13) (scaledMoments[26]?.getD []))
  (clearedOccupancyMoment momentDenominator 13)) = true := by decide
theorem moment_polynomial_13 (M : ℝ) :
 peval (pscale (occupancyScale 13) (scaledMoments[26]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 13) M :=
 checked_equality _ _ moment_cert_13 M
#print axioms moment_cert_13
#print axioms moment_polynomial_13
end V033
