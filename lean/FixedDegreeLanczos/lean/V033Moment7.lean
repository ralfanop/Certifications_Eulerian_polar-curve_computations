import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_7 : pzero (psub
  (pscale (occupancyScale 7) (scaledMoments[14]?.getD []))
  (clearedOccupancyMoment momentDenominator 7)) = true := by decide
theorem moment_polynomial_7 (M : ℝ) :
 peval (pscale (occupancyScale 7) (scaledMoments[14]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 7) M :=
 checked_equality _ _ moment_cert_7 M
#print axioms moment_cert_7
#print axioms moment_polynomial_7
end V033
