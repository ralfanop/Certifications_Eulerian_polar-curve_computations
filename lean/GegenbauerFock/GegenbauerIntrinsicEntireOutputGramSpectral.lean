import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.OutputGramSpectrum
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# V007 — compact positive spectral theorem on true holomorphic Gaussian L²

The true ultraspherical analysis map has codomain the independently
defined closed intrinsic entire Gaussian L² Hilbert subspace. Its
actual output Gram C_hol C_hol† is self-adjoint, positive and compact.
With the locally certified completeness instance, the nonzero
eigenspaces are finite dimensional, all eigenspaces are complete,
and eigenvalues are real and nonnegative.

All assertions concern the actual infinite-dimensional analytic
Hilbert space, not a coefficient-only substitute or finite matrix.
-/

noncomputable section
open MeasureTheory Module End
open scoped InnerProduct ComplexConjugate

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Self-adjointness of the actual output Gram in the complete
intrinsic entire Gaussian L² Hilbert space. -/
theorem C_intrinsicEntire_outputGram_selfadjoint
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
      (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
     (C_intrinsicEntire_outputGram lam alpha hlam ha).adjoint =
       C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  change (((C_intrinsicEntire lam alpha hlam ha).comp
    (C_intrinsicEntire lam alpha hlam ha).adjoint)).adjoint =
    (C_intrinsicEntire lam alpha hlam ha).comp
      (C_intrinsicEntire lam alpha hlam ha).adjoint
  simp

/-- The actual holomorphic output Gram is positive in Mathlib's
operator-order sense, not just as a scalar numerical form. -/
theorem C_intrinsicEntire_outputGram_isPositive
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C_intrinsicEntire_outputGram lam alpha hlam ha).IsPositive := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  have hadj :
      ((C_intrinsicEntire lam alpha hlam ha).adjoint).adjoint =
        C_intrinsicEntire lam alpha hlam ha := by
    simp
  have hpositive :
      (((C_intrinsicEntire lam alpha hlam ha).adjoint).adjoint ∘L
        (C_intrinsicEntire lam alpha hlam ha).adjoint).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self
      (C_intrinsicEntire lam alpha hlam ha).adjoint
  rw [hadj] at hpositive
  exact hpositive

/-- Inner-product symmetry of the genuine analytic output Gram,
as required by the infinite-dimensional compact spectral theorem. -/
theorem C_intrinsicEntire_outputGram_symmetric
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    ((C_intrinsicEntire_outputGram lam alpha hlam ha :
      GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
        GaussianArea.entireGaussianL2Submodule alpha) :
      GaussianArea.entireGaussianL2Submodule alpha →ₗ[ℂ]
        GaussianArea.entireGaussianL2Submodule alpha).IsSymmetric := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  exact ContinuousLinearMap.isSelfAdjoint_iff'.mpr
    (C_intrinsicEntire_outputGram_selfadjoint lam alpha hlam ha)

/-- Nonzero eigenspaces of the true compact holomorphic output Gram
have finite Hilbert multiplicity. -/
theorem C_intrinsicEntire_outputGram_nonzero_eigenspace_finite
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ) (hmu : mu ≠ 0) :
    FiniteDimensional ℂ
      (eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact ContinuousLinearMap.finite_dimensional_eigenspace
    (C_intrinsicEntire_outputGram_compact lam alpha hlam ha) mu hmu

/-- All eigenspaces of the compact self-adjoint holomorphic output
Gram have dense sum in the genuine entire Gaussian L² Hilbert space. -/
theorem C_intrinsicEntire_outputGram_eigenspaces_complete
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (⨆ mu : ℂ,
      eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu)ᗮ =
      (⊥ : Submodule ℂ (GaussianArea.entireGaussianL2Submodule alpha)) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (C_intrinsicEntire_outputGram_compact lam alpha hlam ha)
    (C_intrinsicEntire_outputGram_symmetric lam alpha hlam ha)

/-- Every eigenvalue of the genuine analytic output Gram is real. -/
theorem C_intrinsicEntire_outputGram_eigenvalue_real
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℂ)
    (hmu : HasEigenvalue
      (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu) :
    conj mu = mu := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact LinearMap.IsSymmetric.conj_eigenvalue_eq_self
    (C_intrinsicEntire_outputGram_symmetric lam alpha hlam ha) hmu

/-- Every real eigenvalue of the positive analytic output Gram
is nonnegative. -/
theorem C_intrinsicEntire_outputGram_real_eigenvalue_nonneg
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (mu : ℝ)
    (hmu : HasEigenvalue
      (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap mu) :
    0 ≤ mu := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  apply eigenvalue_nonneg_of_nonneg hmu
  intro F
  exact (C_intrinsicEntire_outputGram_isPositive lam alpha hlam ha).re_inner_nonneg_right F

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_selfadjoint
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_isPositive
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_symmetric
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_nonzero_eigenspace_finite
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_eigenspaces_complete
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_eigenvalue_real
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_real_eigenvalue_nonneg

end GegenbauerFock.GeneralUltrasphericalFock
