import GegenbauerFock.OutputGramSpectrum

/-!
# V007 — actual normalized singular pairs of the ultraspherical Fock transform

For each positive REAL eigenvalue μ of G = C†C and any unit source
eigenvector f, the normalized coefficient vector
  F = (sqrt μ)⁻¹ • C f
has unit norm and satisfies
  C f = sqrt μ • F,   C† F = sqrt μ • f.
These are genuine singular-vector equations in infinite Hilbert spaces.
No assumption that C is injective or has dense range is imposed.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- The exact norm-energy relation for an actual REAL source Gram
eigenvector, independently of any chosen basis. -/
theorem C_gram_real_eigenvector_norm_sq
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖C lam alpha hlam ha f‖ ^ 2 = mu * ‖f‖ ^ 2 := by
  calc
    ‖C lam alpha hlam ha f‖ ^ 2 =
        RCLike.re (inner ℂ (gram lam alpha hlam ha f) f) :=
      HilbertGram.gram_norm_sq (C lam alpha hlam ha) f
    _ = mu * ‖f‖ ^ 2 := by
      rw [h, inner_smul_left, inner_self_eq_norm_sq_to_K]
      simp

/-- A unit eigenvector with positive eigenvalue μ is sent by C to a
vector of norm sqrt μ. -/
theorem C_unit_gram_eigenvector_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : ‖f‖ = 1)
    (h : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖C lam alpha hlam ha f‖ = Real.sqrt mu := by
  have hsq := C_gram_real_eigenvector_norm_sq
    lam alpha hlam ha mu f h
  rw [hf, one_pow, mul_one] at hsq
  apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  simpa [Real.sq_sqrt hmu.le] using hsq

/-- The normalized target vector constructed from a positive source
Gram eigenvector has unit norm, with no finite-dimensional proxy. -/
theorem C_normalized_singular_target_unit
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : ‖f‖ = 1)
    (h : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)‖ = 1 := by
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs,
    C_unit_gram_eigenvector_norm lam alpha hlam ha mu hmu f hf h]
  exact inv_mul_cancel₀ hs.ne'

/-- The first normalized singular-pair equation: C f = sqrt μ F. -/
theorem C_normalized_singular_pair_right
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    (Real.sqrt mu : ℂ) •
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) =
        C lam alpha hlam ha f := by
  have hs : (Real.sqrt mu : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hmu).ne'
  rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

/-- The second normalized singular-pair equation: C† F = sqrt μ f. -/
theorem C_normalized_singular_pair_left
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    C_adjoint lam alpha hlam ha
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) =
        (Real.sqrt mu : ℂ) • f := by
  have hs : (Real.sqrt mu : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hmu).ne'
  have hsq : (Real.sqrt mu : ℂ) ^ 2 = (mu : ℂ) := by
    exact_mod_cast Real.sq_sqrt hmu.le
  change C_adjoint lam alpha hlam ha
    ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f) = _
  rw [map_smul]
  change (Real.sqrt mu : ℂ)⁻¹ •
    gram lam alpha hlam ha f = _
  rw [h, smul_smul, ← hsq, pow_two, ← mul_assoc,
    inv_mul_cancel₀ hs, one_mul]

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_gram_real_eigenvector_norm_sq
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_unit_gram_eigenvector_norm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_normalized_singular_target_unit
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_normalized_singular_pair_right
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_normalized_singular_pair_left

end GegenbauerFock.GeneralUltrasphericalFock
