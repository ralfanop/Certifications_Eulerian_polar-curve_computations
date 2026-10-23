import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_9 : coeff9[9]?.getD [] = monicDen9 := by decide
theorem orthog_cert_9_0 : pzero (momentCombination scaledMoments coeff9 0) = true := by decide
theorem orthog_9_0 (M : ℝ) : realCombination scaledMoments M coeff9 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_0 M
theorem orthog_cert_9_1 : pzero (momentCombination scaledMoments coeff9 1) = true := by decide
theorem orthog_9_1 (M : ℝ) : realCombination scaledMoments M coeff9 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_1 M
theorem orthog_cert_9_2 : pzero (momentCombination scaledMoments coeff9 2) = true := by decide
theorem orthog_9_2 (M : ℝ) : realCombination scaledMoments M coeff9 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_2 M
theorem orthog_cert_9_3 : pzero (momentCombination scaledMoments coeff9 3) = true := by decide
theorem orthog_9_3 (M : ℝ) : realCombination scaledMoments M coeff9 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_3 M
theorem orthog_cert_9_4 : pzero (momentCombination scaledMoments coeff9 4) = true := by decide
theorem orthog_9_4 (M : ℝ) : realCombination scaledMoments M coeff9 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_4 M
theorem orthog_cert_9_5 : pzero (momentCombination scaledMoments coeff9 5) = true := by decide
theorem orthog_9_5 (M : ℝ) : realCombination scaledMoments M coeff9 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_5 M
theorem orthog_cert_9_6 : pzero (momentCombination scaledMoments coeff9 6) = true := by decide
theorem orthog_9_6 (M : ℝ) : realCombination scaledMoments M coeff9 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_6 M
theorem orthog_cert_9_7 : pzero (momentCombination scaledMoments coeff9 7) = true := by decide
theorem orthog_9_7 (M : ℝ) : realCombination scaledMoments M coeff9 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_7 M
theorem orthog_cert_9_8 : pzero (momentCombination scaledMoments coeff9 8) = true := by decide
theorem orthog_9_8 (M : ℝ) : realCombination scaledMoments M coeff9 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_9_8 M
theorem norm_cert_9 : pzero (psub (momentCombination scaledMoments coeff9 9) normNum9) = true := by decide
theorem ratio_cert_9 : pzero (psub (pmul (pmul betaNum9 normNum8) monicDen9)
 (pmul (pmul betaDen9 normNum9) monicDen8)) = true := by decide
theorem ratio_9 (M : ℝ) (hD : peval betaDen9 M ≠ 0) (hH : peval normNum8 M ≠ 0)
 (hC : peval monicDen9 M ≠ 0) (hCp : peval monicDen8 M ≠ 0) :
 peval betaNum9 M / peval betaDen9 M =
 (peval normNum9 M / peval monicDen9 M) / (peval normNum8 M / peval monicDen8 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_9 M hD hH hC hCp
#print axioms ratio_cert_9
#print axioms ratio_9
end V033
