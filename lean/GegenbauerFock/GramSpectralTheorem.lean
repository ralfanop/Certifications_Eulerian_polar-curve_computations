import GegenbauerFock.GramIntegralComplete
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# V007: actual compact self-adjoint Gram spectral theorem

This specializes Mathlib's infinite-dimensional compact
self-adjoint spectral theorem to the complete Gegenbauer-Fock
exponential Bochner integral operator. Nonzero eigenspaces are
finite-dimensional and the eigenspaces have dense linear span.
These claims do not assume a finite matrix approximation.
-/

open MeasureTheory Module End WithLp
open scoped InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The concrete exponential integral Gram map is a compact operator. -/
theorem gramIntegralOperator_compact (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (gramIntegralOperator lam alpha hlam ha) := by
  rw [← gram_eq_gramIntegralOperator lam alpha hlam ha]
  exact gram_compact_concrete lam alpha hlam ha

/-- The complete bounded Gram kernel operator is self-adjoint. -/
theorem gramIntegralOperator_selfadjoint (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) :
    (gramIntegralOperator lam alpha hlam ha).adjoint =
      gramIntegralOperator lam alpha hlam ha := by
  rw [← gram_eq_gramIntegralOperator lam alpha hlam ha]
  exact gram_selfadjoint lam alpha hlam ha

/-- The Gram kernel operator is self-adjoint in the sesquilinear
(inner-product) sense needed for infinite spectral theory. -/
theorem gramIntegralOperator_symmetric (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) :
    ((gramIntegralOperator lam alpha hlam ha) :
      Lp ℂ 2 (Ultraspherical.measure lam) →ₗ[ℂ]
        Lp ℂ 2 (Ultraspherical.measure lam)).IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    (gramIntegralOperator_selfadjoint lam alpha hlam ha)

/-- The nonzero eigenspaces of the actual compact integral Gram
operator are finite-dimensional, for any complex eigenvalue. -/
theorem gramIntegralOperator_nonzero_eigenspace_finite
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ
      (eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) := by
  exact (gramIntegralOperator_compact lam alpha hlam ha)
    .finite_dimensional_eigenspace mu hmu

/-- The closed sum of all actual Gram integral eigenspaces is the
full ultraspherical L²: spectral completeness in infinite dimension. -/
theorem gramIntegralOperator_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)ᗮ =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  exact (gramIntegralOperator_compact lam alpha hlam ha)
    .orthogonalComplement_iSup_eigenspaces_eq_bot
      (gramIntegralOperator_symmetric lam alpha hlam ha)

/-- Every eigenvalue of the compact self-adjoint Gram operator
is real in the complex-conjugation sense. -/
theorem gramIntegralOperator_eigenvalue_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmu : HasEigenvalue
      (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) :
    conj mu = mu := by
  exact (gramIntegralOperator_symmetric lam alpha hlam ha)
    .conj_eigenvalue_eq_self hmu

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_compact
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_selfadjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_nonzero_eigenspace_finite
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_eigenspaces_complete
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_eigenvalue_real

end GegenbauerFock.GeneralUltrasphericalFock
