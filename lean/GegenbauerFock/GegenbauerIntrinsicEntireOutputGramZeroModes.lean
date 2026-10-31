import GegenbauerFock.GegenbauerIntrinsicEntireOutputGram
import GegenbauerFock.OutputEntireCoefficientUniqueness
import GegenbauerFock.OutputGramZeroModes

/-!
# V007 — zero-mode exclusion in the genuine intrinsic Fock output Gram

The true Gegenbauer–Fock map has a Hilbert adjoint between distinct
complete Hilbert spaces, the ultraspherical L² source and the
independently defined intrinsic entire Gaussian L² target. The exact
formula for this adjoint combines with the previously certified
coefficient-space adjoint injectivity to rule out all nonzero
holomorphic Gaussian output zero modes.

This does not assert surjectivity of the compact ultraspherical
transform, nor absence of zero from the operator spectrum.
-/

noncomputable section
open MeasureTheory Module End

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The TRUE Hilbert adjoint of the Gegenbauer transform valued in
intrinsic entire Gaussian Fock L² is injective, by coefficient analytic
uniqueness and the certified onto Bargmann–Fock synthesis. -/
theorem C_intrinsicEntire_adjoint_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C_intrinsicEntire_adjoint lam alpha hlam ha) := by
  intro F G h
  rw [C_intrinsicEntire_adjoint_apply,
      C_intrinsicEntire_adjoint_apply] at h
  apply (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).symm.injective
  exact C_adjoint_injective_unconditional lam alpha hlam ha h

/-- Exact closed kernel correspondence on the real Gaussian
holomorphic output Hilbert space: ker(C_hol C_hol†) = ker(C_hol†). -/
theorem C_intrinsicEntire_outputGram_ker_eq_adjoint_ker
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C_intrinsicEntire_outputGram lam alpha hlam ha).ker =
      (C_intrinsicEntire_adjoint lam alpha hlam ha).ker := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  change ((C_intrinsicEntire lam alpha hlam ha).comp
    (C_intrinsicEntire lam alpha hlam ha).adjoint).ker =
      (C_intrinsicEntire lam alpha hlam ha).adjoint.ker
  exact (C_intrinsicEntire lam alpha hlam ha).ker_self_comp_adjoint

/-- No nonzero intrinsic entire Gaussian L² vector is annihilated by
the true analytic-output Gram. -/
theorem C_intrinsicEntire_outputGram_ker_bot
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    (C_intrinsicEntire_outputGram lam alpha hlam ha).ker =
      (⊥ : Submodule ℂ (GaussianArea.entireGaussianL2Submodule alpha)) := by
  rw [C_intrinsicEntire_outputGram_ker_eq_adjoint_ker]
  exact LinearMap.ker_eq_bot.mpr
    (C_intrinsicEntire_adjoint_injective lam alpha hlam ha)

/-- Zero is NOT an eigenvalue of the genuine holomorphic Fock OUTPUT
Gram, even though the compact operator may have zero in its spectrum. -/
theorem C_intrinsicEntire_outputGram_zero_eigenspace_bot
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    eigenspace (C_intrinsicEntire_outputGram lam alpha hlam ha).toLinearMap 0 =
      (⊥ : Submodule ℂ (GaussianArea.entireGaussianL2Submodule alpha)) := by
  rw [eigenspace_zero]
  exact C_intrinsicEntire_outputGram_ker_bot lam alpha hlam ha

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_adjoint_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_ker_eq_adjoint_ker
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_ker_bot
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_zero_eigenspace_bot

end GegenbauerFock.GeneralUltrasphericalFock
