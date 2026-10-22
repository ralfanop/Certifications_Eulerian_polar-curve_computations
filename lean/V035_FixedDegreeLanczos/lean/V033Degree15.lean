import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_15 : coeff15[15]?.getD [] = monicDen15 := by decide
theorem orthog_cert_15_0 : pzero (momentCombination scaledMoments coeff15 0) = true := by decide
theorem orthog_15_0 (M : ℝ) : realCombination scaledMoments M coeff15 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_0 M
theorem orthog_cert_15_1 : pzero (momentCombination scaledMoments coeff15 1) = true := by decide
theorem orthog_15_1 (M : ℝ) : realCombination scaledMoments M coeff15 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_1 M
theorem orthog_cert_15_2 : pzero (momentCombination scaledMoments coeff15 2) = true := by decide
theorem orthog_15_2 (M : ℝ) : realCombination scaledMoments M coeff15 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_2 M
theorem orthog_cert_15_3 : pzero (momentCombination scaledMoments coeff15 3) = true := by decide
theorem orthog_15_3 (M : ℝ) : realCombination scaledMoments M coeff15 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_3 M
theorem orthog_cert_15_4 : pzero (momentCombination scaledMoments coeff15 4) = true := by decide
theorem orthog_15_4 (M : ℝ) : realCombination scaledMoments M coeff15 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_4 M
theorem orthog_cert_15_5 : pzero (momentCombination scaledMoments coeff15 5) = true := by decide
theorem orthog_15_5 (M : ℝ) : realCombination scaledMoments M coeff15 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_5 M
theorem orthog_cert_15_6 : pzero (momentCombination scaledMoments coeff15 6) = true := by decide
theorem orthog_15_6 (M : ℝ) : realCombination scaledMoments M coeff15 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_6 M
theorem orthog_cert_15_7 : pzero (momentCombination scaledMoments coeff15 7) = true := by decide
theorem orthog_15_7 (M : ℝ) : realCombination scaledMoments M coeff15 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_7 M
theorem orthog_cert_15_8 : pzero (momentCombination scaledMoments coeff15 8) = true := by decide
theorem orthog_15_8 (M : ℝ) : realCombination scaledMoments M coeff15 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_8 M
theorem orthog_cert_15_9 : pzero (momentCombination scaledMoments coeff15 9) = true := by decide
theorem orthog_15_9 (M : ℝ) : realCombination scaledMoments M coeff15 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_9 M
theorem orthog_cert_15_10 : pzero (momentCombination scaledMoments coeff15 10) = true := by decide
theorem orthog_15_10 (M : ℝ) : realCombination scaledMoments M coeff15 10 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_10 M
theorem orthog_cert_15_11 : pzero (momentCombination scaledMoments coeff15 11) = true := by decide
theorem orthog_15_11 (M : ℝ) : realCombination scaledMoments M coeff15 11 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_11 M
theorem orthog_cert_15_12 : pzero (momentCombination scaledMoments coeff15 12) = true := by decide
theorem orthog_15_12 (M : ℝ) : realCombination scaledMoments M coeff15 12 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_12 M
theorem orthog_cert_15_13 : pzero (momentCombination scaledMoments coeff15 13) = true := by decide
theorem orthog_15_13 (M : ℝ) : realCombination scaledMoments M coeff15 13 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_13 M
theorem orthog_cert_15_14 : pzero (momentCombination scaledMoments coeff15 14) = true := by decide
theorem orthog_15_14 (M : ℝ) : realCombination scaledMoments M coeff15 14 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_15_14 M
theorem norm_cert_15 : pzero (psub (momentCombination scaledMoments coeff15 15) normNum15) = true := by decide
theorem ratio_cert_15 : pzero (psub (pmul (pmul betaNum15 normNum14) monicDen15)
 (pmul (pmul betaDen15 normNum15) monicDen14)) = true := by decide
theorem ratio_15 (M : ℝ) (hD : peval betaDen15 M ≠ 0) (hH : peval normNum14 M ≠ 0)
 (hC : peval monicDen15 M ≠ 0) (hCp : peval monicDen14 M ≠ 0) :
 peval betaNum15 M / peval betaDen15 M =
 (peval normNum15 M / peval monicDen15 M) / (peval normNum14 M / peval monicDen14 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_15 M hD hH hC hCp
#print axioms ratio_cert_15
#print axioms ratio_15
end V033
