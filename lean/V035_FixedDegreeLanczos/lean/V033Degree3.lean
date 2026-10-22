import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_3 : coeff3[3]?.getD [] = monicDen3 := by decide
theorem orthog_cert_3_0 : pzero (momentCombination scaledMoments coeff3 0) = true := by decide
theorem orthog_3_0 (M : ℝ) : realCombination scaledMoments M coeff3 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_3_0 M
theorem orthog_cert_3_1 : pzero (momentCombination scaledMoments coeff3 1) = true := by decide
theorem orthog_3_1 (M : ℝ) : realCombination scaledMoments M coeff3 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_3_1 M
theorem orthog_cert_3_2 : pzero (momentCombination scaledMoments coeff3 2) = true := by decide
theorem orthog_3_2 (M : ℝ) : realCombination scaledMoments M coeff3 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_3_2 M
theorem norm_cert_3 : pzero (psub (momentCombination scaledMoments coeff3 3) normNum3) = true := by decide
end V033
