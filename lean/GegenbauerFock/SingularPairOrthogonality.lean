import GegenbauerFock.SingularPairOutputEigen

/-!
# V007 — orthogonality of singular pairs on a positive Gram eigenspace

This establishes an inner-product property of the *actual* bounded
Gegenbauer--Fock transform, rather than relying on finite truncations.
It is an incremental step towards selecting orthonormal singular
families within nonzero finite-dimensional spectral subspaces.

No claim of global singular-system completeness, injectivity or
density of either range is made.
-/

noncomputable section

namespace GegenbauerFock.GeneralUltrasphericalFock

open MeasureTheory

/-- Orthogonal source vectors remain orthogonal after applying C when
the first source vector belongs to a real Gram eigenspace. The result
does not require the second vector to lie in that eigenspace. -/
theorem C_preserves_gram_eigenvector_orthogonality
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = (mu : ℂ) • f)
    (hfg : inner ℂ f g = 0) :
    inner ℂ (C lam alpha hlam ha f)
      (C lam alpha hlam ha g) = 0 := by
  calc
    inner ℂ (C lam alpha hlam ha f)
      (C lam alpha hlam ha g) =
        inner ℂ (gram lam alpha hlam ha f) g :=
      (HilbertGram.gram_inner (C lam alpha hlam ha) f g).symm
    _ = inner ℂ ((mu : ℂ) • f) g := by rw [hf]
    _ = 0 := by rw [inner_smul_left, hfg]; simp

/-- Orthogonality of normalized Fock-side singular vectors in the
same strictly positive Gram eigenspace. -/
theorem normalized_singular_targets_orthogonal
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ) (hmu : 0 < mu)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hf : gram lam alpha hlam ha f = (mu : ℂ) • f)
    (hfg : inner ℂ f g = 0) :
    inner ℂ
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha f)
      ((Real.sqrt mu : ℂ)⁻¹ • C lam alpha hlam ha g) = 0 := by
  rw [inner_smul_left, inner_smul_right,
    C_preserves_gram_eigenvector_orthogonality lam alpha hlam ha mu f g hf hfg]
  simp

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_preserves_gram_eigenvector_orthogonality
#print axioms GegenbauerFock.GeneralUltrasphericalFock.normalized_singular_targets_orthogonal

end GegenbauerFock.GeneralUltrasphericalFock
