import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_2 : coeff2[2]?.getD [] = monicDen2 := by decide
theorem orthog_cert_2_0 : pzero (momentCombination scaledMoments coeff2 0) = true := by decide
theorem orthog_2_0 (M : ℝ) : realCombination scaledMoments M coeff2 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_2_0 M
theorem orthog_cert_2_1 : pzero (momentCombination scaledMoments coeff2 1) = true := by decide
theorem orthog_2_1 (M : ℝ) : realCombination scaledMoments M coeff2 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_2_1 M
theorem norm_cert_2 : pzero (psub (momentCombination scaledMoments coeff2 2) normNum2) = true := by decide
end V033
