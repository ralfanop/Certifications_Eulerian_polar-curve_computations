import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GeneralUltrasphericalFock
import GegenbauerFock.CompactFockProperDenseRange

/-!
# V007 — the genuine Gegenbauer transform valued in entire Gaussian Fock L²

The independently certified onto Gaussian Bargmann–Fock isometry
transports the already bounded ultraspherical coefficient transform
to the intrinsic Gaussian holomorphic Hilbert subspace. This is
not an assertion that the compact Gegenbauer transform itself is
surjective: the latter has proper dense range.

The codomain consists of actual Gaussian L² classes with entire
representatives, rather than a formal sequence surrogate.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The true ultraspherical transform taking values in the independently
defined intrinsic entire Gaussian L² Hilbert space. -/
noncomputable def C_intrinsicEntire
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Lp ℂ 2 (Ultraspherical.measure lam) →L[ℂ]
      GaussianArea.entireGaussianL2Submodule alpha :=
  (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).toLinearIsometry.toContinuousLinearMap.comp
    (C lam alpha hlam ha)

/-- Its value is exactly the entire Gaussian synthesis of the true
factorially normalized Gegenbauer Fourier coefficient vector. -/
theorem C_intrinsicEntire_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    C_intrinsicEntire lam alpha hlam ha f =
      GaussianArea.coefficientIntrinsicEntireEquiv alpha ha
        (C lam alpha hlam ha f) := rfl

/-- The analytic realization preserves the exact Hilbert norm of the
full infinite Gegenbauer–Fock coefficient transform. -/
theorem C_intrinsicEntire_norm
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ‖C_intrinsicEntire lam alpha hlam ha f‖ =
      ‖C lam alpha hlam ha f‖ := by
  rw [C_intrinsicEntire_apply]
  exact (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).norm_map _

/-- Injectivity survives the identification of coefficients with
genuine entire Gaussian L² classes. -/
theorem C_intrinsicEntire_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha) :
    Function.Injective (C_intrinsicEntire lam alpha hlam ha) := by
  intro f g h
  apply C_injective lam alpha hlam ha
  apply (GaussianArea.coefficientIntrinsicEntireEquiv alpha ha).injective
  simpa only [C_intrinsicEntire_apply] using h

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_norm
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_injective

end GegenbauerFock.GeneralUltrasphericalFock
