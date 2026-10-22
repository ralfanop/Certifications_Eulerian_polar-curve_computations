import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_6 : coeff6[6]?.getD [] = monicDen6 := by decide
theorem orthog_cert_6_0 : pzero (momentCombination scaledMoments coeff6 0) = true := by decide
theorem orthog_6_0 (M : ℝ) : realCombination scaledMoments M coeff6 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_6_0 M
theorem orthog_cert_6_1 : pzero (momentCombination scaledMoments coeff6 1) = true := by decide
theorem orthog_6_1 (M : ℝ) : realCombination scaledMoments M coeff6 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_6_1 M
theorem orthog_cert_6_2 : pzero (momentCombination scaledMoments coeff6 2) = true := by decide
theorem orthog_6_2 (M : ℝ) : realCombination scaledMoments M coeff6 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_6_2 M
theorem orthog_cert_6_3 : pzero (momentCombination scaledMoments coeff6 3) = true := by decide
theorem orthog_6_3 (M : ℝ) : realCombination scaledMoments M coeff6 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_6_3 M
theorem orthog_cert_6_4 : pzero (momentCombination scaledMoments coeff6 4) = true := by decide
theorem orthog_6_4 (M : ℝ) : realCombination scaledMoments M coeff6 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_6_4 M
theorem orthog_cert_6_5 : pzero (momentCombination scaledMoments coeff6 5) = true := by decide
theorem orthog_6_5 (M : ℝ) : realCombination scaledMoments M coeff6 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_6_5 M
theorem norm_cert_6 : pzero (psub (momentCombination scaledMoments coeff6 6) normNum6) = true := by decide
theorem ratio_cert_6 : pzero (psub (pmul (pmul betaNum6 normNum5) monicDen6)
 (pmul (pmul betaDen6 normNum6) monicDen5)) = true := by decide
theorem ratio_6 (M : ℝ) (hD : peval betaDen6 M ≠ 0) (hH : peval normNum5 M ≠ 0)
 (hC : peval monicDen6 M ≠ 0) (hCp : peval monicDen5 M ≠ 0) :
 peval betaNum6 M / peval betaDen6 M =
 (peval normNum6 M / peval monicDen6 M) / (peval normNum5 M / peval monicDen5 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_6 M hD hH hC hCp
#print axioms ratio_cert_6
#print axioms ratio_6
end V033
