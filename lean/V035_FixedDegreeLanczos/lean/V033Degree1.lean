import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_1 : coeff1[1]?.getD [] = monicDen1 := by decide
theorem orthog_cert_1_0 : pzero (momentCombination scaledMoments coeff1 0) = true := by decide
theorem orthog_1_0 (M : ℝ) : realCombination scaledMoments M coeff1 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_1_0 M
theorem norm_cert_1 : pzero (psub (momentCombination scaledMoments coeff1 1) normNum1) = true := by decide
end V033
