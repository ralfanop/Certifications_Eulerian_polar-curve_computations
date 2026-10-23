import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_11 : pzero (psub
  (pscale (occupancyScale 11) (scaledMoments[22]?.getD []))
  (clearedOccupancyMoment momentDenominator 11)) = true := by decide
theorem moment_polynomial_11 (M : ℝ) :
 peval (pscale (occupancyScale 11) (scaledMoments[22]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 11) M :=
 checked_equality _ _ moment_cert_11 M
#print axioms moment_cert_11
#print axioms moment_polynomial_11
end V033
