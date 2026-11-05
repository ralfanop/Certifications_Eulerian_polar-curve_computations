import GegenbauerFock.GegenbauerIntrinsicEntireGramIdentity
import GegenbauerFock.GramSpectralTheorem
import GegenbauerFock.GramSpectralKernel
import GegenbauerFock.CompactQuasiaffinity

/-!
# V007 — full spectral transfer for the genuine entire Gaussian Fock source Gram

The certified operator equality between the intrinsic holomorphic
Gegenbauer–Fock source Gram and the actual ultraspherical Bochner
exponential-kernel operator transfers their compact selfadjoint
positive spectral theory, including real nonnegative eigenvalues,
nonzero finite-dimensional eigenspaces, and spectral completeness.

Injectivity of the concrete ultraspherical analysis transform shows
that zero has no eigenvectors. This does not claim that zero is absent
from the spectrum of the compact operator on infinite-dimensional L².
-/

noncomputable section
open MeasureTheory Module End
open scoped InnerProduct ComplexConjugate

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The genuine intrinsic-holomorphic source Gram is compact. -/
theorem C_intrinsicEntire_gram_compact
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (C_intrinsicEntire_gram lam alpha hlam ha) := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha]
  exact gramIntegralOperator_compact lam alpha hlam ha

/-- Self-adjointness of the genuine intrinsic-holomorphic source Gram. -/
theorem C_intrinsicEntire_gram_selfadjoint
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C_intrinsicEntire_gram lam alpha hlam ha).adjoint =
      C_intrinsicEntire_gram lam alpha hlam ha := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha]
  exact gramIntegralOperator_selfadjoint lam alpha hlam ha

/-- Mathlib positivity on the actual source Hilbert-space operator. -/
theorem C_intrinsicEntire_gram_isPositive
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C_intrinsicEntire_gram lam alpha hlam ha).IsPositive := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha]
  exact gramIntegralOperator_isPositive lam alpha hlam ha

/-- Each nonzero eigenspace of the true intrinsic Gaussian Fock source
Gram is finite dimensional, including its genuine multiplicity. -/
theorem C_intrinsicEntire_gram_nonzero_eigenspace_finite
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ
      (eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap mu) := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha]
  exact gramIntegralOperator_nonzero_eigenspace_finite lam alpha hlam ha mu hmu

/-- The orthogonal complement of the sum of all genuine holomorphic
source-Gram eigenspaces is zero in the complete source L² Hilbert space. -/
theorem C_intrinsicEntire_gram_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
      eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha]
  exact gramIntegralOperator_eigenspaces_complete lam alpha hlam ha

/-- All eigenvalues of the true intrinsic source Gram are real. -/
theorem C_intrinsicEntire_gram_eigenvalue_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmu : HasEigenvalue
      (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap mu) :
    conj mu = mu := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha] at hmu
  exact gramIntegralOperator_eigenvalue_real lam alpha hlam ha mu hmu

/-- Real eigenvalues of the genuine intrinsic source Gram are nonnegative. -/
theorem C_intrinsicEntire_gram_real_eigenvalue_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ)
    (hmu : HasEigenvalue
      (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap mu) :
    0 ≤ mu := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha] at hmu
  exact gramIntegralOperator_real_eigenvalue_nonneg lam alpha hlam ha mu hmu

/-- The eigenvalue zero has trivial eigenspace, because the original
ultraspherical coefficient transform is injective. A compact infinite-
dimensional Gram can nevertheless have zero in its spectrum. -/
theorem C_intrinsicEntire_gram_zero_eigenspace_bot
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (C_intrinsicEntire_gram lam alpha hlam ha).toLinearMap 0 =
      (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  rw [C_intrinsicEntire_gram_eq_integralOperator lam alpha hlam ha]
  rw [gramIntegralOperator_zero_eigenspace_eq_C_ker lam alpha hlam ha]
  exact LinearMap.ker_eq_bot.mpr (C_injective lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_compact
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_selfadjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_isPositive
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_nonzero_eigenspace_finite
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eigenspaces_complete
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_eigenvalue_real
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_real_eigenvalue_nonneg
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_gram_zero_eigenspace_bot

end GegenbauerFock.GeneralUltrasphericalFock
