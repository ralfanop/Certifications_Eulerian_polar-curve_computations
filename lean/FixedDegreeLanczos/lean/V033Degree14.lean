import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_14 : coeff14[14]?.getD [] = monicDen14 := by decide
theorem orthog_cert_14_0 : pzero (momentCombination scaledMoments coeff14 0) = true := by decide
theorem orthog_14_0 (M : ℝ) : realCombination scaledMoments M coeff14 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_0 M
theorem orthog_cert_14_1 : pzero (momentCombination scaledMoments coeff14 1) = true := by decide
theorem orthog_14_1 (M : ℝ) : realCombination scaledMoments M coeff14 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_1 M
theorem orthog_cert_14_2 : pzero (momentCombination scaledMoments coeff14 2) = true := by decide
theorem orthog_14_2 (M : ℝ) : realCombination scaledMoments M coeff14 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_2 M
theorem orthog_cert_14_3 : pzero (momentCombination scaledMoments coeff14 3) = true := by decide
theorem orthog_14_3 (M : ℝ) : realCombination scaledMoments M coeff14 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_3 M
theorem orthog_cert_14_4 : pzero (momentCombination scaledMoments coeff14 4) = true := by decide
theorem orthog_14_4 (M : ℝ) : realCombination scaledMoments M coeff14 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_4 M
theorem orthog_cert_14_5 : pzero (momentCombination scaledMoments coeff14 5) = true := by decide
theorem orthog_14_5 (M : ℝ) : realCombination scaledMoments M coeff14 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_5 M
theorem orthog_cert_14_6 : pzero (momentCombination scaledMoments coeff14 6) = true := by decide
theorem orthog_14_6 (M : ℝ) : realCombination scaledMoments M coeff14 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_6 M
theorem orthog_cert_14_7 : pzero (momentCombination scaledMoments coeff14 7) = true := by decide
theorem orthog_14_7 (M : ℝ) : realCombination scaledMoments M coeff14 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_7 M
theorem orthog_cert_14_8 : pzero (momentCombination scaledMoments coeff14 8) = true := by decide
theorem orthog_14_8 (M : ℝ) : realCombination scaledMoments M coeff14 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_8 M
theorem orthog_cert_14_9 : pzero (momentCombination scaledMoments coeff14 9) = true := by decide
theorem orthog_14_9 (M : ℝ) : realCombination scaledMoments M coeff14 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_9 M
theorem orthog_cert_14_10 : pzero (momentCombination scaledMoments coeff14 10) = true := by decide
theorem orthog_14_10 (M : ℝ) : realCombination scaledMoments M coeff14 10 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_10 M
theorem orthog_cert_14_11 : pzero (momentCombination scaledMoments coeff14 11) = true := by decide
theorem orthog_14_11 (M : ℝ) : realCombination scaledMoments M coeff14 11 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_11 M
theorem orthog_cert_14_12 : pzero (momentCombination scaledMoments coeff14 12) = true := by decide
theorem orthog_14_12 (M : ℝ) : realCombination scaledMoments M coeff14 12 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_12 M
theorem orthog_cert_14_13 : pzero (momentCombination scaledMoments coeff14 13) = true := by decide
theorem orthog_14_13 (M : ℝ) : realCombination scaledMoments M coeff14 13 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_14_13 M
theorem norm_cert_14 : pzero (psub (momentCombination scaledMoments coeff14 14) normNum14) = true := by decide
theorem ratio_cert_14 : pzero (psub (pmul (pmul betaNum14 normNum13) monicDen14)
 (pmul (pmul betaDen14 normNum14) monicDen13)) = true := by decide
theorem ratio_14 (M : ℝ) (hD : peval betaDen14 M ≠ 0) (hH : peval normNum13 M ≠ 0)
 (hC : peval monicDen14 M ≠ 0) (hCp : peval monicDen13 M ≠ 0) :
 peval betaNum14 M / peval betaDen14 M =
 (peval normNum14 M / peval monicDen14 M) / (peval normNum13 M / peval monicDen13 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_14 M hD hH hC hCp
#print axioms ratio_cert_14
#print axioms ratio_14
end V033
