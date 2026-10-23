import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_10 : coeff10[10]?.getD [] = monicDen10 := by decide
theorem orthog_cert_10_0 : pzero (momentCombination scaledMoments coeff10 0) = true := by decide
theorem orthog_10_0 (M : ℝ) : realCombination scaledMoments M coeff10 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_0 M
theorem orthog_cert_10_1 : pzero (momentCombination scaledMoments coeff10 1) = true := by decide
theorem orthog_10_1 (M : ℝ) : realCombination scaledMoments M coeff10 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_1 M
theorem orthog_cert_10_2 : pzero (momentCombination scaledMoments coeff10 2) = true := by decide
theorem orthog_10_2 (M : ℝ) : realCombination scaledMoments M coeff10 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_2 M
theorem orthog_cert_10_3 : pzero (momentCombination scaledMoments coeff10 3) = true := by decide
theorem orthog_10_3 (M : ℝ) : realCombination scaledMoments M coeff10 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_3 M
theorem orthog_cert_10_4 : pzero (momentCombination scaledMoments coeff10 4) = true := by decide
theorem orthog_10_4 (M : ℝ) : realCombination scaledMoments M coeff10 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_4 M
theorem orthog_cert_10_5 : pzero (momentCombination scaledMoments coeff10 5) = true := by decide
theorem orthog_10_5 (M : ℝ) : realCombination scaledMoments M coeff10 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_5 M
theorem orthog_cert_10_6 : pzero (momentCombination scaledMoments coeff10 6) = true := by decide
theorem orthog_10_6 (M : ℝ) : realCombination scaledMoments M coeff10 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_6 M
theorem orthog_cert_10_7 : pzero (momentCombination scaledMoments coeff10 7) = true := by decide
theorem orthog_10_7 (M : ℝ) : realCombination scaledMoments M coeff10 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_7 M
theorem orthog_cert_10_8 : pzero (momentCombination scaledMoments coeff10 8) = true := by decide
theorem orthog_10_8 (M : ℝ) : realCombination scaledMoments M coeff10 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_8 M
theorem orthog_cert_10_9 : pzero (momentCombination scaledMoments coeff10 9) = true := by decide
theorem orthog_10_9 (M : ℝ) : realCombination scaledMoments M coeff10 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_10_9 M
theorem norm_cert_10 : pzero (psub (momentCombination scaledMoments coeff10 10) normNum10) = true := by decide
theorem ratio_cert_10 : pzero (psub (pmul (pmul betaNum10 normNum9) monicDen10)
 (pmul (pmul betaDen10 normNum10) monicDen9)) = true := by decide
theorem ratio_10 (M : ℝ) (hD : peval betaDen10 M ≠ 0) (hH : peval normNum9 M ≠ 0)
 (hC : peval monicDen10 M ≠ 0) (hCp : peval monicDen9 M ≠ 0) :
 peval betaNum10 M / peval betaDen10 M =
 (peval normNum10 M / peval monicDen10 M) / (peval normNum9 M / peval monicDen9 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_10 M hD hH hC hCp
#print axioms ratio_cert_10
#print axioms ratio_10
end V033
