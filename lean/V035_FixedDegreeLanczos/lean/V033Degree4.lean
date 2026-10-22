import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_4 : coeff4[4]?.getD [] = monicDen4 := by decide
theorem orthog_cert_4_0 : pzero (momentCombination scaledMoments coeff4 0) = true := by decide
theorem orthog_4_0 (M : ℝ) : realCombination scaledMoments M coeff4 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_4_0 M
theorem orthog_cert_4_1 : pzero (momentCombination scaledMoments coeff4 1) = true := by decide
theorem orthog_4_1 (M : ℝ) : realCombination scaledMoments M coeff4 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_4_1 M
theorem orthog_cert_4_2 : pzero (momentCombination scaledMoments coeff4 2) = true := by decide
theorem orthog_4_2 (M : ℝ) : realCombination scaledMoments M coeff4 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_4_2 M
theorem orthog_cert_4_3 : pzero (momentCombination scaledMoments coeff4 3) = true := by decide
theorem orthog_4_3 (M : ℝ) : realCombination scaledMoments M coeff4 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_4_3 M
theorem norm_cert_4 : pzero (psub (momentCombination scaledMoments coeff4 4) normNum4) = true := by decide
end V033
