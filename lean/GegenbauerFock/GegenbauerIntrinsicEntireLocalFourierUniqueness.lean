import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation
import GegenbauerFock.GegenbauerIntrinsicEntireAlphaCoherence
import GegenbauerFock.OutputComplexAnalyticIdentity

/-!
# V007 — Fourier–Bochner uniqueness from a short imaginary-axis interval

The genuine entire Fock transform is determined by its values on a
nontrivial open imaginary interval. The proof uses the certified
holomorphic identity theorem, exact pointwise Bochner formula and
injectivity of the Gegenbauer integral transform. The result holds
even if the two entire outputs belong to different Gaussian Hilbert
spaces. No surjectivity of the compact operator is assumed.
-/

noncomputable section
open MeasureTheory Set

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Two genuine ultraspherical L² inputs are equal if their entire
Bargmann–Fock outputs agree on an open imaginary segment. -/
theorem C_intrinsicEntire_injective_of_imaginary_segment
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hsegment : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f)
        (FockAnalyticRestriction.imaginaryPoint alpha u) =
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g)
        (FockAnalyticRestriction.imaginaryPoint alpha u)) :
    f = g := by
  let F : ℂ → ℂ := fun z =>
    GaussianArea.entireRepresentative alpha
      (C_intrinsicEntire lam alpha hlam ha f) z -
    GaussianArea.entireRepresentative alpha
      (C_intrinsicEntire lam alpha hlam ha g) z
  have hdiff : Differentiable ℂ F :=
    (GaussianArea.entireRepresentative_differentiable alpha
      (C_intrinsicEntire lam alpha hlam ha f)).sub
    (GaussianArea.entireRepresentative_differentiable alpha
      (C_intrinsicEntire lam alpha hlam ha g))
  have hzero : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      F (FockAnalyticRestriction.imaginaryPoint alpha u) = 0 := by
    intro u hu
    change GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f)
        (FockAnalyticRestriction.imaginaryPoint alpha u) -
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g)
        (FockAnalyticRestriction.imaginaryPoint alpha u) = 0
    exact sub_eq_zero.mpr (hsegment u hu)
  have hident : F = 0 :=
    FockAnalyticRestriction.entire_eq_zero_of_imaginary_interior_zero
      alpha ha F hdiff hzero
  have hrep :
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) =
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g) := by
    funext z
    have hz := congrFun hident z
    change GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) z -
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g) z = 0 at hz
    exact sub_eq_zero.mp hz
  apply C_intrinsicEntire_injective lam alpha hlam ha
  exact GaussianArea.entireRepresentative_injective alpha hrep

/-- Equality of actual Fourier–Bochner integrals solely on the
imaginary open interval already forces equality of L² inputs. -/
theorem ultraspherical_fourierBochner_injective_on_imaginary_segment
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hsegment : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      (∫ v : ℝ, f v *
        Complex.exp (Complex.I *
          FockAnalyticRestriction.imaginaryPoint alpha u *
          (v : ℂ) / 2) ∂(Ultraspherical.measure lam)) =
      (∫ v : ℝ, g v *
        Complex.exp (Complex.I *
          FockAnalyticRestriction.imaginaryPoint alpha u *
          (v : ℂ) / 2) ∂(Ultraspherical.measure lam))) :
    f = g := by
  apply C_intrinsicEntire_injective_of_imaginary_segment
    lam alpha hlam ha f g
  intro u hu
  rw [C_intrinsicEntire_pointwiseBochner,
    C_intrinsicEntire_pointwiseBochner]
  exact hsegment u hu

/-- Comparing entire outputs in two distinct Gaussian Fock Hilbert
spaces on a short imaginary interval still determines the input. -/
theorem C_intrinsicEntire_crossAlpha_injective_of_imaginary_segment
    (lam alpha beta : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (hb : 0 < beta)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (hsegment : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f)
        (FockAnalyticRestriction.imaginaryPoint alpha u) =
      GaussianArea.entireRepresentative beta
        (C_intrinsicEntire lam beta hlam hb g)
        (FockAnalyticRestriction.imaginaryPoint alpha u)) :
    f = g := by
  apply C_intrinsicEntire_injective_of_imaginary_segment
    lam alpha hlam ha f g
  intro u hu
  exact (hsegment u hu).trans
    (C_intrinsicEntire_pointwise_independent_of_alpha
      lam alpha beta hlam ha hb g
      (FockAnalyticRestriction.imaginaryPoint alpha u)).symm

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_injective_of_imaginary_segment
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_injective_on_imaginary_segment
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_crossAlpha_injective_of_imaginary_segment

end GegenbauerFock.GeneralUltrasphericalFock
