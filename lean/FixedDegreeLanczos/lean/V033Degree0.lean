import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_0 : coeff0[0]?.getD [] = monicDen0 := by decide
theorem norm_cert_0 : pzero (psub (momentCombination scaledMoments coeff0 0) normNum0) = true := by decide
end V033
