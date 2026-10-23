import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_8 : coeff8[8]?.getD [] = monicDen8 := by decide
theorem orthog_cert_8_0 : pzero (momentCombination scaledMoments coeff8 0) = true := by decide
theorem orthog_8_0 (M : ℝ) : realCombination scaledMoments M coeff8 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_0 M
theorem orthog_cert_8_1 : pzero (momentCombination scaledMoments coeff8 1) = true := by decide
theorem orthog_8_1 (M : ℝ) : realCombination scaledMoments M coeff8 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_1 M
theorem orthog_cert_8_2 : pzero (momentCombination scaledMoments coeff8 2) = true := by decide
theorem orthog_8_2 (M : ℝ) : realCombination scaledMoments M coeff8 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_2 M
theorem orthog_cert_8_3 : pzero (momentCombination scaledMoments coeff8 3) = true := by decide
theorem orthog_8_3 (M : ℝ) : realCombination scaledMoments M coeff8 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_3 M
theorem orthog_cert_8_4 : pzero (momentCombination scaledMoments coeff8 4) = true := by decide
theorem orthog_8_4 (M : ℝ) : realCombination scaledMoments M coeff8 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_4 M
theorem orthog_cert_8_5 : pzero (momentCombination scaledMoments coeff8 5) = true := by decide
theorem orthog_8_5 (M : ℝ) : realCombination scaledMoments M coeff8 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_5 M
theorem orthog_cert_8_6 : pzero (momentCombination scaledMoments coeff8 6) = true := by decide
theorem orthog_8_6 (M : ℝ) : realCombination scaledMoments M coeff8 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_6 M
theorem orthog_cert_8_7 : pzero (momentCombination scaledMoments coeff8 7) = true := by decide
theorem orthog_8_7 (M : ℝ) : realCombination scaledMoments M coeff8 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_8_7 M
theorem norm_cert_8 : pzero (psub (momentCombination scaledMoments coeff8 8) normNum8) = true := by decide
theorem ratio_cert_8 : pzero (psub (pmul (pmul betaNum8 normNum7) monicDen8)
 (pmul (pmul betaDen8 normNum8) monicDen7)) = true := by decide
theorem ratio_8 (M : ℝ) (hD : peval betaDen8 M ≠ 0) (hH : peval normNum7 M ≠ 0)
 (hC : peval monicDen8 M ≠ 0) (hCp : peval monicDen7 M ≠ 0) :
 peval betaNum8 M / peval betaDen8 M =
 (peval normNum8 M / peval monicDen8 M) / (peval normNum7 M / peval monicDen7 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_8 M hD hH hC hCp
#print axioms ratio_cert_8
#print axioms ratio_8
end V033
