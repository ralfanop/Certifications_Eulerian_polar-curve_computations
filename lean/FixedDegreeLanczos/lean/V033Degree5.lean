import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_5 : coeff5[5]?.getD [] = monicDen5 := by decide
theorem orthog_cert_5_0 : pzero (momentCombination scaledMoments coeff5 0) = true := by decide
theorem orthog_5_0 (M : ℝ) : realCombination scaledMoments M coeff5 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_5_0 M
theorem orthog_cert_5_1 : pzero (momentCombination scaledMoments coeff5 1) = true := by decide
theorem orthog_5_1 (M : ℝ) : realCombination scaledMoments M coeff5 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_5_1 M
theorem orthog_cert_5_2 : pzero (momentCombination scaledMoments coeff5 2) = true := by decide
theorem orthog_5_2 (M : ℝ) : realCombination scaledMoments M coeff5 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_5_2 M
theorem orthog_cert_5_3 : pzero (momentCombination scaledMoments coeff5 3) = true := by decide
theorem orthog_5_3 (M : ℝ) : realCombination scaledMoments M coeff5 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_5_3 M
theorem orthog_cert_5_4 : pzero (momentCombination scaledMoments coeff5 4) = true := by decide
theorem orthog_5_4 (M : ℝ) : realCombination scaledMoments M coeff5 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_5_4 M
theorem norm_cert_5 : pzero (psub (momentCombination scaledMoments coeff5 5) normNum5) = true := by decide
theorem ratio_cert_5 : pzero (psub (pmul (pmul betaNum5 normNum4) monicDen5)
 (pmul (pmul betaDen5 normNum5) monicDen4)) = true := by decide
theorem ratio_5 (M : ℝ) (hD : peval betaDen5 M ≠ 0) (hH : peval normNum4 M ≠ 0)
 (hC : peval monicDen5 M ≠ 0) (hCp : peval monicDen4 M ≠ 0) :
 peval betaNum5 M / peval betaDen5 M =
 (peval normNum5 M / peval monicDen5 M) / (peval normNum4 M / peval monicDen4 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_5 M hD hH hC hCp
#print axioms ratio_cert_5
#print axioms ratio_5
end V033
