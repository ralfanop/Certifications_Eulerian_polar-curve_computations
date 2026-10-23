import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_12 : coeff12[12]?.getD [] = monicDen12 := by decide
theorem orthog_cert_12_0 : pzero (momentCombination scaledMoments coeff12 0) = true := by decide
theorem orthog_12_0 (M : ℝ) : realCombination scaledMoments M coeff12 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_0 M
theorem orthog_cert_12_1 : pzero (momentCombination scaledMoments coeff12 1) = true := by decide
theorem orthog_12_1 (M : ℝ) : realCombination scaledMoments M coeff12 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_1 M
theorem orthog_cert_12_2 : pzero (momentCombination scaledMoments coeff12 2) = true := by decide
theorem orthog_12_2 (M : ℝ) : realCombination scaledMoments M coeff12 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_2 M
theorem orthog_cert_12_3 : pzero (momentCombination scaledMoments coeff12 3) = true := by decide
theorem orthog_12_3 (M : ℝ) : realCombination scaledMoments M coeff12 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_3 M
theorem orthog_cert_12_4 : pzero (momentCombination scaledMoments coeff12 4) = true := by decide
theorem orthog_12_4 (M : ℝ) : realCombination scaledMoments M coeff12 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_4 M
theorem orthog_cert_12_5 : pzero (momentCombination scaledMoments coeff12 5) = true := by decide
theorem orthog_12_5 (M : ℝ) : realCombination scaledMoments M coeff12 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_5 M
theorem orthog_cert_12_6 : pzero (momentCombination scaledMoments coeff12 6) = true := by decide
theorem orthog_12_6 (M : ℝ) : realCombination scaledMoments M coeff12 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_6 M
theorem orthog_cert_12_7 : pzero (momentCombination scaledMoments coeff12 7) = true := by decide
theorem orthog_12_7 (M : ℝ) : realCombination scaledMoments M coeff12 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_7 M
theorem orthog_cert_12_8 : pzero (momentCombination scaledMoments coeff12 8) = true := by decide
theorem orthog_12_8 (M : ℝ) : realCombination scaledMoments M coeff12 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_8 M
theorem orthog_cert_12_9 : pzero (momentCombination scaledMoments coeff12 9) = true := by decide
theorem orthog_12_9 (M : ℝ) : realCombination scaledMoments M coeff12 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_9 M
theorem orthog_cert_12_10 : pzero (momentCombination scaledMoments coeff12 10) = true := by decide
theorem orthog_12_10 (M : ℝ) : realCombination scaledMoments M coeff12 10 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_10 M
theorem orthog_cert_12_11 : pzero (momentCombination scaledMoments coeff12 11) = true := by decide
theorem orthog_12_11 (M : ℝ) : realCombination scaledMoments M coeff12 11 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_12_11 M
theorem norm_cert_12 : pzero (psub (momentCombination scaledMoments coeff12 12) normNum12) = true := by decide
theorem ratio_cert_12 : pzero (psub (pmul (pmul betaNum12 normNum11) monicDen12)
 (pmul (pmul betaDen12 normNum12) monicDen11)) = true := by decide
theorem ratio_12 (M : ℝ) (hD : peval betaDen12 M ≠ 0) (hH : peval normNum11 M ≠ 0)
 (hC : peval monicDen12 M ≠ 0) (hCp : peval monicDen11 M ≠ 0) :
 peval betaNum12 M / peval betaDen12 M =
 (peval normNum12 M / peval monicDen12 M) / (peval normNum11 M / peval monicDen11 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_12 M hD hH hC hCp
#print axioms ratio_cert_12
#print axioms ratio_12
end V033
