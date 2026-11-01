import GegenbauerFock.SingularPairNormalization

/-!
# V007 — normalized singular vectors are eigenvectors of the output Gram

A strictly separate consequence of the previously formalized source
Gram eigenvector normalization. The genuine output Gram C C† has the
same positive eigenvalue and the target vector has unit norm.

No enumeration of spectral multiplicities or density-of-range
assumption is made. Existing certified modules remain unchanged.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The unit target singular vector induced by any positive real
source-Gram eigenpair is an eigenvector of the actual infinite
coefficient-space Gram, with the same positive eigenvalue. -/
theorem outputGram_normalized_singular_eigenvector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    outputGram lam alpha hlam ha
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) =
      (mu : ℂ) •
        ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) := by
  have hs : (Real.sqrt mu : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hmu).ne'
  have hsq : (Real.sqrt mu : ℂ) ^ 2 = (mu : ℂ) := by
    exact_mod_cast Real.sq_sqrt hmu.le
  have hfactor :
      (mu : ℂ) * (Real.sqrt mu : ℂ)⁻¹ = (Real.sqrt mu : ℂ) := by
    rw [← hsq, pow_two, mul_assoc, mul_inv_cancel₀ hs, mul_one]
  change C lam alpha hlam ha
    (C_adjoint lam alpha hlam ha
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)) = _
  rw [C_normalized_singular_pair_left lam alpha hlam ha mu hmu f h,
      map_smul, smul_smul, hfactor]

/-- Both normalized singular-pair equations, the target unit norm,
and its positive output-Gram eigen-equation hold simultaneously. -/
theorem normalized_singular_pair_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : ‖f‖ = 1)
    (h : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)‖ = 1 ∧
    (Real.sqrt mu : ℂ) •
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) =
      C lam alpha hlam ha f ∧
    C_adjoint lam alpha hlam ha
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) =
      (Real.sqrt mu : ℂ) • f ∧
    outputGram lam alpha hlam ha
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) =
      (mu : ℂ) •
        ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) := by
  exact ⟨C_normalized_singular_target_unit lam alpha hlam ha mu hmu f hf h,
    C_normalized_singular_pair_right lam alpha hlam ha mu hmu f,
    C_normalized_singular_pair_left lam alpha hlam ha mu hmu f h,
    outputGram_normalized_singular_eigenvector lam alpha hlam ha mu hmu f h⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.outputGram_normalized_singular_eigenvector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.normalized_singular_pair_complete

end GegenbauerFock.GeneralUltrasphericalFock
