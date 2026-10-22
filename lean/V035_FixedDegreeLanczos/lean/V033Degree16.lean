import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_16 : coeff16[16]?.getD [] = monicDen16 := by decide
theorem orthog_cert_16_0 : pzero (momentCombination scaledMoments coeff16 0) = true := by decide
theorem orthog_16_0 (M : ℝ) : realCombination scaledMoments M coeff16 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_0 M
theorem orthog_cert_16_1 : pzero (momentCombination scaledMoments coeff16 1) = true := by decide
theorem orthog_16_1 (M : ℝ) : realCombination scaledMoments M coeff16 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_1 M
theorem orthog_cert_16_2 : pzero (momentCombination scaledMoments coeff16 2) = true := by decide
theorem orthog_16_2 (M : ℝ) : realCombination scaledMoments M coeff16 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_2 M
theorem orthog_cert_16_3 : pzero (momentCombination scaledMoments coeff16 3) = true := by decide
theorem orthog_16_3 (M : ℝ) : realCombination scaledMoments M coeff16 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_3 M
theorem orthog_cert_16_4 : pzero (momentCombination scaledMoments coeff16 4) = true := by decide
theorem orthog_16_4 (M : ℝ) : realCombination scaledMoments M coeff16 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_4 M
theorem orthog_cert_16_5 : pzero (momentCombination scaledMoments coeff16 5) = true := by decide
theorem orthog_16_5 (M : ℝ) : realCombination scaledMoments M coeff16 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_5 M
theorem orthog_cert_16_6 : pzero (momentCombination scaledMoments coeff16 6) = true := by decide
theorem orthog_16_6 (M : ℝ) : realCombination scaledMoments M coeff16 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_6 M
theorem orthog_cert_16_7 : pzero (momentCombination scaledMoments coeff16 7) = true := by decide
theorem orthog_16_7 (M : ℝ) : realCombination scaledMoments M coeff16 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_7 M
theorem orthog_cert_16_8 : pzero (momentCombination scaledMoments coeff16 8) = true := by decide
theorem orthog_16_8 (M : ℝ) : realCombination scaledMoments M coeff16 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_8 M
theorem orthog_cert_16_9 : pzero (momentCombination scaledMoments coeff16 9) = true := by decide
theorem orthog_16_9 (M : ℝ) : realCombination scaledMoments M coeff16 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_9 M
theorem orthog_cert_16_10 : pzero (momentCombination scaledMoments coeff16 10) = true := by decide
theorem orthog_16_10 (M : ℝ) : realCombination scaledMoments M coeff16 10 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_10 M
theorem orthog_cert_16_11 : pzero (momentCombination scaledMoments coeff16 11) = true := by decide
theorem orthog_16_11 (M : ℝ) : realCombination scaledMoments M coeff16 11 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_11 M
theorem orthog_cert_16_12 : pzero (momentCombination scaledMoments coeff16 12) = true := by decide
theorem orthog_16_12 (M : ℝ) : realCombination scaledMoments M coeff16 12 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_12 M
theorem orthog_cert_16_13 : pzero (momentCombination scaledMoments coeff16 13) = true := by decide
theorem orthog_16_13 (M : ℝ) : realCombination scaledMoments M coeff16 13 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_13 M
theorem orthog_cert_16_14 : pzero (momentCombination scaledMoments coeff16 14) = true := by decide
theorem orthog_16_14 (M : ℝ) : realCombination scaledMoments M coeff16 14 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_14 M
theorem orthog_cert_16_15 : pzero (momentCombination scaledMoments coeff16 15) = true := by decide
theorem orthog_16_15 (M : ℝ) : realCombination scaledMoments M coeff16 15 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_16_15 M
theorem norm_cert_16 : pzero (psub (momentCombination scaledMoments coeff16 16) normNum16) = true := by decide
theorem ratio_cert_16 : pzero (psub (pmul (pmul betaNum16 normNum15) monicDen16)
 (pmul (pmul betaDen16 normNum16) monicDen15)) = true := by decide
theorem ratio_16 (M : ℝ) (hD : peval betaDen16 M ≠ 0) (hH : peval normNum15 M ≠ 0)
 (hC : peval monicDen16 M ≠ 0) (hCp : peval monicDen15 M ≠ 0) :
 peval betaNum16 M / peval betaDen16 M =
 (peval normNum16 M / peval monicDen16 M) / (peval normNum15 M / peval monicDen15 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_16 M hD hH hC hCp
#print axioms ratio_cert_16
#print axioms ratio_16
end V033
