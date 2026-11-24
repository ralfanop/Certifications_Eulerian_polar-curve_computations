import M15Cert.CarliniLaplace

/-!
# Manuscript 15, 24 November 2026: Eulerian–Lambert critical threshold

Source: Manuscript_15_20261124_EDITORIALE_EQUAZIONI_COMPLETE(1).zip
ZIP SHA256 e9dea5546bca52a3a88001c3e29c4caa7ac62325446a30c3b0fa54a2aa9d2acd
15.tex SHA256 e3b6632886cf881c46decf051f19169486229b4168fe97fb011398e38ee4b396

This independent module reuses the certified critical root uStar and constant
lambdaCL from M15Cert.CarliniLaplace. It establishes exact scalar identities
in Proposition "Eulerian–Lambert representation of the catenoidal threshold".
The general logarithmic derivative and uniqueness of the generalized Lambert
branch are separate proof obligations, not silently assumed here.
-/

namespace M15

/-- The removable real Eulerian profile r_E(2 i u). -/
noncomputable def eulerianPhi (u : ℝ) : ℝ :=
  if u = 0 then 1 else Real.sinh u / u

/-- The restriction to the imaginary axis of the entire Eulerian kernel. -/
theorem eulerianPhi_eq_rEc (u : ℝ) :
    (eulerianPhi u : ℂ) = rEc (2 * Complex.I * u) := by
  exact (rEc_two_I_mul u).symm

/-- The true critical constant is the reciprocal of uStar times the
Eulerian profile, not an unverified numerical approximation. -/
theorem lambdaCL_eulerian_critical :
    lambdaCL = 1 / (uStar * eulerianPhi uStar) := by
  have hu : uStar ≠ 0 := uStar_pos.ne'
  have hs : Real.sinh uStar ≠ 0 := sinh_uStar_pos.ne'
  rw [lambdaCL_eq.1]
  simp only [eulerianPhi, hu, ↓reduceIte]
  field_simp

/-- Real Langevin function on the punctured positive axis. -/
noncomputable def langevinReal (u : ℝ) : ℝ :=
  Real.cosh u / Real.sinh u - 1 / u

/-- Critical Eulerian–Langevin identity of the new proposition. -/
theorem langevin_critical_identity :
    uStar * langevinReal uStar = lambdaCL ^ 2 := by
  have hu : uStar ≠ 0 := uStar_pos.ne'
  have hs : Real.sinh uStar ≠ 0 := sinh_uStar_pos.ne'
  have hpos : 0 ≤ uStar ^ 2 - 1 := by
    have hb := uStar_bounds.1
    nlinarith [sq_nonneg (uStar - 1)]
  have hsq : lambdaCL ^ 2 = uStar ^ 2 - 1 := by
    rw [lambdaCL_eq.2, Real.sq_sqrt hpos]
  rw [hsq]
  unfold langevinReal
  rw [cosh_uStar]
  field_simp
  ring

/-- The generalized Lambert relation at wStar = 2 * uStar. -/
theorem lambert_at_threshold :
    ((2 * uStar - 2) / (2 * uStar + 2)) * Real.exp (2 * uStar) = 1 := by
  have he : Real.exp uStar = Real.cosh uStar + Real.sinh uStar := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hn : Real.exp (-uStar) = Real.cosh uStar - Real.sinh uStar := by
    rw [Real.cosh_eq, Real.sinh_eq]
    ring
  have hsplit : (uStar - 1) * Real.exp uStar =
      (uStar + 1) * Real.exp (-uStar) := by
    rw [he, hn, cosh_uStar]
    ring
  have hm : Real.exp (-uStar) * Real.exp uStar = 1 := by
    rw [← Real.exp_add]
    simp
  have h2 : Real.exp (2 * uStar) = Real.exp uStar * Real.exp uStar := by
    rw [show 2 * uStar = uStar + uStar by ring, Real.exp_add]
  have hroot : (uStar - 1) * Real.exp (2 * uStar) = uStar + 1 := by
    calc
      (uStar - 1) * Real.exp (2 * uStar) =
          ((uStar - 1) * Real.exp uStar) * Real.exp uStar := by rw [h2]; ring
      _ = ((uStar + 1) * Real.exp (-uStar)) * Real.exp uStar := by rw [hsplit]
      _ = uStar + 1 := by rw [mul_assoc, hm, mul_one]
  have hden : (2 * uStar + 2 : ℝ) ≠ 0 := by linarith [uStar_pos]
  calc
    ((2 * uStar - 2) / (2 * uStar + 2)) * Real.exp (2 * uStar) =
        ((2 * uStar - 2) * Real.exp (2 * uStar)) / (2 * uStar + 2) := by ring
    _ = 1 := by
      apply (div_eq_iff hden).2
      nlinarith [hroot]

/-- The positive generalized Lambert parameter lies strictly above two. -/
theorem lambert_parameter_gt_two : (2 : ℝ) < 2 * uStar := by
  nlinarith [uStar_bounds.1]

/-- Reconstruction of lambdaCL from the generalized Lambert parameter. -/
theorem lambdaCL_from_lambert_parameter :
    lambdaCL = Real.sqrt ((2 * uStar) ^ 2 / 4 - 1) := by
  rw [lambdaCL_eq.2]
  congr 1
  ring

#print axioms M15.eulerianPhi_eq_rEc
#print axioms M15.lambdaCL_eulerian_critical
#print axioms M15.langevin_critical_identity
#print axioms M15.lambert_at_threshold
#print axioms M15.lambert_parameter_gt_two
#print axioms M15.lambdaCL_from_lambert_parameter

end M15
