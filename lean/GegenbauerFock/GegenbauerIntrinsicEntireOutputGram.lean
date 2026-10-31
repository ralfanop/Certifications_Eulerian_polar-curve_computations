import GegenbauerFock.GegenbauerIntrinsicEntireCompactQuasiaffinity
import GegenbauerFock.GegenbauerIntrinsicEntireGramPairing
import GegenbauerFock.GramSingularTransfer

/-!
# V007 — genuine output Gram in the intrinsic entire Gaussian Fock space

The full Bargmann–Fock synthesis U : ℓ² ≃ₗᵢ intrinsicEntireGaussianL²
is onto, with a previously certified analytic Gaussian L² range and
locally proved Hilbert completeness. Hence the true Hilbert adjoint of
the concrete ultraspherical operator C_hol = U ∘ C exists.

The output Gram here is the actual C_hol C_hol† on the intrinsic
holomorphic Hilbert space, not an operator on ambient nonholomorphic
Gaussian L². Its pointwise formula is the unitary conjugation
U (C C†) U⁻¹, proved from the genuine Hilbert adjoint pairing.
This never asserts that the compact transform C_hol itself is onto.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true Hilbert adjoint of the concrete ultraspherical transform
valued in the complete intrinsic entire Gaussian L² Fock Hilbert space. -/
noncomputable def C_intrinsicEntire_adjoint
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure lam) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  exact (C_intrinsicEntire lam alpha hlam ha).adjoint

/-- The true analytic-output Hilbert adjoint is the coefficient-side
adjoint composed with the inverse of the certified onto Bargmann–Fock
synthesis isometry, pointwise on every genuine entire Gaussian L² class. -/
theorem C_intrinsicEntire_adjoint_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : GaussianArea.entireGaussianL2Submodule alpha) :
    C_intrinsicEntire_adjoint lam alpha hlam ha F =
      C_adjoint lam alpha hlam ha
        ((GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).symm F) := by
  letI : CompleteSpace (GaussianArea.entireGaussianL2Submodule alpha) :=
    (GaussianArea.intrinsicEntire_isClosed alpha ha).completeSpace_coe
  apply ext_inner_right ℂ
  intro f
  let U := GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
  calc
    inner ℂ (C_intrinsicEntire_adjoint lam alpha hlam ha F) f =
        inner ℂ F (C_intrinsicEntire lam alpha hlam ha f) := by
          exact (C_intrinsicEntire lam alpha hlam ha).adjoint_inner_left f F
    _ = inner ℂ F (U (C lam alpha hlam ha f)) := by
          rw [C_intrinsicEntire_apply]
    _ = inner ℂ (U.symm F) (C lam alpha hlam ha f) := by
          simpa only [U.apply_symm_apply] using
            (U.inner_map_map (U.symm F) (C lam alpha hlam ha f))
    _ = inner ℂ
          (C_adjoint lam alpha hlam ha (U.symm F)) f := by
          exact (C_adjoint_pairing lam alpha hlam ha (U.symm F) f).symm

/-- The genuine intrinsic entire Gaussian Fock OUTPUT Gram C_hol C_hol†
is a bounded operator on the actual entire Gaussian L² Hilbert space. -/
noncomputable def C_intrinsicEntire_outputGram
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    GaussianArea.entireGaussianL2Submodule alpha →L[ℂ]
      GaussianArea.entireGaussianL2Submodule alpha :=
  (C_intrinsicEntire lam alpha hlam ha).comp
    (C_intrinsicEntire_adjoint lam alpha hlam ha)

/-- The actual intrinsic holomorphic output Gram is exactly the unitary
conjugate U (C C†) U⁻¹ of the coefficient-space output Gram. -/
theorem C_intrinsicEntire_outputGram_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (F : GaussianArea.entireGaussianL2Submodule alpha) :
    C_intrinsicEntire_outputGram lam alpha hlam ha F =
      (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha)
        (outputGram lam alpha hlam ha
          ((GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).symm F)) := by
  change C_intrinsicEntire lam alpha hlam ha
    (C_intrinsicEntire_adjoint lam alpha hlam ha F) = _
  rw [C_intrinsicEntire_adjoint_apply, C_intrinsicEntire_apply]
  rfl

/-- The genuine analytic-output Gram is compact by composition of the
proved compact Gegenbauer–Fock transform with its bounded adjoint. -/
theorem C_intrinsicEntire_outputGram_compact
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    IsCompactOperator (C_intrinsicEntire_outputGram lam alpha hlam ha) := by
  change IsCompactOperator
    ((C_intrinsicEntire lam alpha hlam ha).comp
      (C_intrinsicEntire_adjoint lam alpha hlam ha))
  exact (C_intrinsicEntire_compact lam alpha hlam ha).comp_clm
    (C_intrinsicEntire_adjoint lam alpha hlam ha)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_adjoint_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_outputGram_compact

end GegenbauerFock.GeneralUltrasphericalFock
