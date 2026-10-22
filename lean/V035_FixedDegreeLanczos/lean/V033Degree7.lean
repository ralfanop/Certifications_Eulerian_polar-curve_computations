import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_7 : coeff7[7]?.getD [] = monicDen7 := by decide
theorem orthog_cert_7_0 : pzero (momentCombination scaledMoments coeff7 0) = true := by decide
theorem orthog_7_0 (M : ℝ) : realCombination scaledMoments M coeff7 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_0 M
theorem orthog_cert_7_1 : pzero (momentCombination scaledMoments coeff7 1) = true := by decide
theorem orthog_7_1 (M : ℝ) : realCombination scaledMoments M coeff7 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_1 M
theorem orthog_cert_7_2 : pzero (momentCombination scaledMoments coeff7 2) = true := by decide
theorem orthog_7_2 (M : ℝ) : realCombination scaledMoments M coeff7 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_2 M
theorem orthog_cert_7_3 : pzero (momentCombination scaledMoments coeff7 3) = true := by decide
theorem orthog_7_3 (M : ℝ) : realCombination scaledMoments M coeff7 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_3 M
theorem orthog_cert_7_4 : pzero (momentCombination scaledMoments coeff7 4) = true := by decide
theorem orthog_7_4 (M : ℝ) : realCombination scaledMoments M coeff7 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_4 M
theorem orthog_cert_7_5 : pzero (momentCombination scaledMoments coeff7 5) = true := by decide
theorem orthog_7_5 (M : ℝ) : realCombination scaledMoments M coeff7 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_5 M
theorem orthog_cert_7_6 : pzero (momentCombination scaledMoments coeff7 6) = true := by decide
theorem orthog_7_6 (M : ℝ) : realCombination scaledMoments M coeff7 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_7_6 M
theorem norm_cert_7 : pzero (psub (momentCombination scaledMoments coeff7 7) normNum7) = true := by decide
theorem ratio_cert_7 : pzero (psub (pmul (pmul betaNum7 normNum6) monicDen7)
 (pmul (pmul betaDen7 normNum7) monicDen6)) = true := by decide
theorem ratio_7 (M : ℝ) (hD : peval betaDen7 M ≠ 0) (hH : peval normNum6 M ≠ 0)
 (hC : peval monicDen7 M ≠ 0) (hCp : peval monicDen6 M ≠ 0) :
 peval betaNum7 M / peval betaDen7 M =
 (peval normNum7 M / peval monicDen7 M) / (peval normNum6 M / peval monicDen6 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_7 M hD hH hC hCp
#print axioms ratio_cert_7
#print axioms ratio_7
end V033
