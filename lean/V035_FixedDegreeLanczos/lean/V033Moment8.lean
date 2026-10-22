import V033MomentSpec
import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem moment_cert_8 : pzero (psub
  (pscale (occupancyScale 8) (scaledMoments[16]?.getD []))
  (clearedOccupancyMoment momentDenominator 8)) = true := by decide
theorem moment_polynomial_8 (M : ℝ) :
 peval (pscale (occupancyScale 8) (scaledMoments[16]?.getD [])) M =
 peval (clearedOccupancyMoment momentDenominator 8) M :=
 checked_equality _ _ moment_cert_8 M
#print axioms moment_cert_8
#print axioms moment_polynomial_8
end V033
