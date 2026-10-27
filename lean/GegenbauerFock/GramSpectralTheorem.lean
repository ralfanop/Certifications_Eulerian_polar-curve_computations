import GegenbauerFock.GramIntegralComplete
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# V007: actual compact self-adjoint Gram spectral theorem

This specializes Mathlib's infinite-dimensional compact
self-adjoint spectral theorem to the complete Gegenbauer-Fock
exponential Bochner integral operator. Nonzero eigenspaces are
finite-dimensional and the eigenspaces have dense linear span.
These claims do not assume a finite matrix approximation.
-/

open MeasureTheory Module End WithLp
open scoped InnerProduct ComplexConjugate

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

/-- Positivity of the genuine L² exponential-kernel operator as a
Mathlib positive continuous linear map, not only nonnegativity
of one scalar quadratic form. -/
theorem gramIntegralOperator_isPositive
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (gramIntegralOperator lam alpha hlam ha).IsPositive := by
  rw [← gram_eq_gramIntegralOperator lam alpha hlam ha]
  change ((C lam alpha hlam ha).adjoint ∘L
    (C lam alpha hlam ha)).IsPositive
  exact ContinuousLinearMap.isPositive_adjoint_comp_self
    (C lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_isPositive

/-- The nonzero eigenspaces of the actual compact integral Gram
operator are finite-dimensional, for any complex eigenvalue. -/
theorem gramIntegralOperator_nonzero_eigenspace_finite
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ
      (eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) := by
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (gramIntegralOperator_compact lam alpha hlam ha) mu hmu

/-- The closed sum of all actual Gram integral eigenspaces is the
full ultraspherical L²: spectral completeness in infinite dimension. -/
theorem gramIntegralOperator_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)ᗮ =
        (⊥ : Submodule ℂ (Lp ℂ 2 (Ultraspherical.measure lam))) := by
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (gramIntegralOperator_compact lam alpha hlam ha)
    (gramIntegralOperator_symmetric lam alpha hlam ha)

/-- Every eigenvalue of the compact self-adjoint Gram operator
is real in the complex-conjugation sense. -/
theorem gramIntegralOperator_eigenvalue_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmu : HasEigenvalue
      (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) :
    conj mu = mu := by
  exact LinearMap.IsSymmetric.conj_eigenvalue_eq_self
    (gramIntegralOperator_symmetric lam alpha hlam ha) hmu

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_compact
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_selfadjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_nonzero_eigenspace_finite
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_eigenspaces_complete
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_eigenvalue_real

/-- The actual exponential Gram integral operator has nonnegative
quadratic form on every ultraspherical L² vector. -/
theorem gramIntegralOperator_nonnegative_form
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    0 ≤ RCLike.re (inner ℂ
      (gramIntegralOperator lam alpha hlam ha f) f) := by
  rw [← gram_eq_gramIntegralOperator lam alpha hlam ha]
  exact gram_positive lam alpha hlam ha f

/-- Every real eigenvalue of the actual compact positive ultraspherical
Gram integral operator is nonnegative.  This is a spectral consequence
of the certified positivity, not an assertion of injectivity. -/
theorem gramIntegralOperator_real_eigenvalue_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ)
    (hmu : HasEigenvalue
      (gramIntegralOperator lam alpha hlam ha).toLinearMap mu) :
    0 ≤ mu := by
  apply eigenvalue_nonneg_of_nonneg hmu
  intro f
  exact (gramIntegralOperator_isPositive lam alpha hlam ha).re_inner_nonneg_right f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_real_eigenvalue_nonneg

/-- Eigenspaces for distinct complex eigenvalues of the compact
Gram integral operator are mutually orthogonal. -/
theorem gramIntegralOperator_orthogonal_eigenspaces
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    OrthogonalFamily ℂ
      (fun mu : ℂ =>
        eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu)
      (fun mu =>
        (eigenspace (gramIntegralOperator lam alpha hlam ha).toLinearMap mu).subtypeₗᵢ) := by
  exact LinearMap.IsSymmetric.orthogonalFamily_eigenspaces
    (gramIntegralOperator_symmetric lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_nonnegative_form
#print axioms GegenbauerFock.GeneralUltrasphericalFock.gramIntegralOperator_orthogonal_eigenspaces


end GegenbauerFock.GeneralUltrasphericalFock
