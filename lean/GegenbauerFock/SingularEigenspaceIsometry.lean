import GegenbauerFock.SingularPairOrthogonality

/-!
# V007 — isometric singular normalization on a positive Gram eigenspace

Unlike a unit-vector-only normalization, this module proves that the
scaled concrete Gegenbauer--Fock transform preserves norms of *all*
vectors in a fixed positive eigenspace of C†C, and therefore preserves
pairwise distances on that eigenspace.

No density or injectivity of C on the entire source space is assumed.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- A positive real eigenvalue fixes the norm of C on every vector
in its source Gram eigenspace, with no unit-norm hypothesis. -/
theorem C_positive_gram_eigenvector_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖C lam alpha hlam ha f‖ = Real.sqrt mu * ‖f‖ := by
  have hsq :=
    C_gram_real_eigenvector_norm_sq lam alpha hlam ha mu f hf
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt hmu.le]
  exact hsq

/-- The correctly scaled concrete Fock transform preserves the
norm of EVERY vector in a positive eigenspace, not just unit vectors. -/
theorem C_normalized_positive_eigenvector_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = (mu : ℂ) • f) :
    ‖((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)‖ = ‖f‖ := by
  have hs : 0 < Real.sqrt mu := Real.sqrt_pos.2 hmu
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hs,
    C_positive_gram_eigenvector_norm lam alpha hlam ha mu hmu f hf]
  rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]

/-- The normalized transform preserves all distances within each
positive Gram eigenspace: it is an isometry on this subspace even if
the full operator C has nontrivial kernel. -/
theorem C_normalized_positive_eigenspace_dist
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = (mu : ℂ) • f)
    (hg : gram lam alpha hlam ha g = (mu : ℂ) • g) :
    dist ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha g) =
        dist f g := by
  have hsub :
      gram lam alpha hlam ha (f - g) =
        (mu : ℂ) • (f - g) := by
    rw [map_sub, hf, hg, smul_sub]
  calc
    dist ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha g) =
        ‖((Real.sqrt mu : ℂ)⁻¹ •
            C lam alpha hlam ha (f - g))‖ := by
      rw [dist_eq_norm, map_sub, smul_sub]
    _ = ‖f - g‖ :=
      C_normalized_positive_eigenvector_norm
        lam alpha hlam ha mu hmu (f - g) hsub
    _ = dist f g := (dist_eq_norm).symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_positive_gram_eigenvector_norm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_normalized_positive_eigenvector_norm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_normalized_positive_eigenspace_dist

end GegenbauerFock.GeneralUltrasphericalFock
