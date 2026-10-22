import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_13 : coeff13[13]?.getD [] = monicDen13 := by decide
theorem orthog_cert_13_0 : pzero (momentCombination scaledMoments coeff13 0) = true := by decide
theorem orthog_13_0 (M : ℝ) : realCombination scaledMoments M coeff13 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_0 M
theorem orthog_cert_13_1 : pzero (momentCombination scaledMoments coeff13 1) = true := by decide
theorem orthog_13_1 (M : ℝ) : realCombination scaledMoments M coeff13 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_1 M
theorem orthog_cert_13_2 : pzero (momentCombination scaledMoments coeff13 2) = true := by decide
theorem orthog_13_2 (M : ℝ) : realCombination scaledMoments M coeff13 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_2 M
theorem orthog_cert_13_3 : pzero (momentCombination scaledMoments coeff13 3) = true := by decide
theorem orthog_13_3 (M : ℝ) : realCombination scaledMoments M coeff13 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_3 M
theorem orthog_cert_13_4 : pzero (momentCombination scaledMoments coeff13 4) = true := by decide
theorem orthog_13_4 (M : ℝ) : realCombination scaledMoments M coeff13 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_4 M
theorem orthog_cert_13_5 : pzero (momentCombination scaledMoments coeff13 5) = true := by decide
theorem orthog_13_5 (M : ℝ) : realCombination scaledMoments M coeff13 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_5 M
theorem orthog_cert_13_6 : pzero (momentCombination scaledMoments coeff13 6) = true := by decide
theorem orthog_13_6 (M : ℝ) : realCombination scaledMoments M coeff13 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_6 M
theorem orthog_cert_13_7 : pzero (momentCombination scaledMoments coeff13 7) = true := by decide
theorem orthog_13_7 (M : ℝ) : realCombination scaledMoments M coeff13 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_7 M
theorem orthog_cert_13_8 : pzero (momentCombination scaledMoments coeff13 8) = true := by decide
theorem orthog_13_8 (M : ℝ) : realCombination scaledMoments M coeff13 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_8 M
theorem orthog_cert_13_9 : pzero (momentCombination scaledMoments coeff13 9) = true := by decide
theorem orthog_13_9 (M : ℝ) : realCombination scaledMoments M coeff13 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_9 M
theorem orthog_cert_13_10 : pzero (momentCombination scaledMoments coeff13 10) = true := by decide
theorem orthog_13_10 (M : ℝ) : realCombination scaledMoments M coeff13 10 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_10 M
theorem orthog_cert_13_11 : pzero (momentCombination scaledMoments coeff13 11) = true := by decide
theorem orthog_13_11 (M : ℝ) : realCombination scaledMoments M coeff13 11 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_11 M
theorem orthog_cert_13_12 : pzero (momentCombination scaledMoments coeff13 12) = true := by decide
theorem orthog_13_12 (M : ℝ) : realCombination scaledMoments M coeff13 12 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_13_12 M
theorem norm_cert_13 : pzero (psub (momentCombination scaledMoments coeff13 13) normNum13) = true := by decide
theorem ratio_cert_13 : pzero (psub (pmul (pmul betaNum13 normNum12) monicDen13)
 (pmul (pmul betaDen13 normNum13) monicDen12)) = true := by decide
theorem ratio_13 (M : ℝ) (hD : peval betaDen13 M ≠ 0) (hH : peval normNum12 M ≠ 0)
 (hC : peval monicDen13 M ≠ 0) (hCp : peval monicDen12 M ≠ 0) :
 peval betaNum13 M / peval betaDen13 M =
 (peval normNum13 M / peval monicDen13 M) / (peval normNum12 M / peval monicDen12 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_13 M hD hH hC hCp
#print axioms ratio_cert_13
#print axioms ratio_13
end V033
