import V033Data
namespace V033
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
theorem monic_11 : coeff11[11]?.getD [] = monicDen11 := by decide
theorem orthog_cert_11_0 : pzero (momentCombination scaledMoments coeff11 0) = true := by decide
theorem orthog_11_0 (M : ℝ) : realCombination scaledMoments M coeff11 0 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_0 M
theorem orthog_cert_11_1 : pzero (momentCombination scaledMoments coeff11 1) = true := by decide
theorem orthog_11_1 (M : ℝ) : realCombination scaledMoments M coeff11 1 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_1 M
theorem orthog_cert_11_2 : pzero (momentCombination scaledMoments coeff11 2) = true := by decide
theorem orthog_11_2 (M : ℝ) : realCombination scaledMoments M coeff11 2 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_2 M
theorem orthog_cert_11_3 : pzero (momentCombination scaledMoments coeff11 3) = true := by decide
theorem orthog_11_3 (M : ℝ) : realCombination scaledMoments M coeff11 3 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_3 M
theorem orthog_cert_11_4 : pzero (momentCombination scaledMoments coeff11 4) = true := by decide
theorem orthog_11_4 (M : ℝ) : realCombination scaledMoments M coeff11 4 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_4 M
theorem orthog_cert_11_5 : pzero (momentCombination scaledMoments coeff11 5) = true := by decide
theorem orthog_11_5 (M : ℝ) : realCombination scaledMoments M coeff11 5 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_5 M
theorem orthog_cert_11_6 : pzero (momentCombination scaledMoments coeff11 6) = true := by decide
theorem orthog_11_6 (M : ℝ) : realCombination scaledMoments M coeff11 6 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_6 M
theorem orthog_cert_11_7 : pzero (momentCombination scaledMoments coeff11 7) = true := by decide
theorem orthog_11_7 (M : ℝ) : realCombination scaledMoments M coeff11 7 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_7 M
theorem orthog_cert_11_8 : pzero (momentCombination scaledMoments coeff11 8) = true := by decide
theorem orthog_11_8 (M : ℝ) : realCombination scaledMoments M coeff11 8 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_8 M
theorem orthog_cert_11_9 : pzero (momentCombination scaledMoments coeff11 9) = true := by decide
theorem orthog_11_9 (M : ℝ) : realCombination scaledMoments M coeff11 9 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_9 M
theorem orthog_cert_11_10 : pzero (momentCombination scaledMoments coeff11 10) = true := by decide
theorem orthog_11_10 (M : ℝ) : realCombination scaledMoments M coeff11 10 = 0 :=
  checked_orthogonality _ _ _ orthog_cert_11_10 M
theorem norm_cert_11 : pzero (psub (momentCombination scaledMoments coeff11 11) normNum11) = true := by decide
theorem ratio_cert_11 : pzero (psub (pmul (pmul betaNum11 normNum10) monicDen11)
 (pmul (pmul betaDen11 normNum11) monicDen10)) = true := by decide
theorem ratio_11 (M : ℝ) (hD : peval betaDen11 M ≠ 0) (hH : peval normNum10 M ≠ 0)
 (hC : peval monicDen11 M ≠ 0) (hCp : peval monicDen10 M ≠ 0) :
 peval betaNum11 M / peval betaDen11 M =
 (peval normNum11 M / peval monicDen11 M) / (peval normNum10 M / peval monicDen10 M) :=
 checked_norm_ratio _ _ _ _ _ _ ratio_cert_11 M hD hH hC hCp
#print axioms ratio_cert_11
#print axioms ratio_11
end V033
