import GegenbauerFock.GegenbauerIntrinsicEntireAlphaCoherence
import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation

/-!
# V007 — uniqueness of ultraspherical L² input from genuine Fourier–Bochner data

For every positive ultraspherical parameter the actual Fourier–Bochner
transform separates L² source vectors, not merely their coefficient
sequences. Pointwise equality of the complex entire Fourier integrals
forces equality of the source L² classes.

The proof uses the certified exact pointwise Bochner identification,
injectivity of the unique entire Gaussian L² representative, and
injectivity of the compact (non-surjective) ultraspherical operator.

The same uniqueness holds when two entire functions are realized in
distinct Gaussian Fock Hilbert spaces with different positive weights.
No equality between the distinct Gaussian Hilbert-space norms is assumed.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The original complex Fourier–Bochner integral uniquely determines
the ultraspherical L² input, from values at every complex frequency. -/
theorem ultraspherical_fourierBochner_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ z : ℂ,
      (∫ u : ℝ, f u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam)) =
      (∫ u : ℝ, g u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam))) :
    f = g := by
  have hrepresentatives :
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) =
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g) := by
    funext z
    calc
      GaussianArea.entireRepresentative alpha
          (C_intrinsicEntire lam alpha hlam ha f) z =
        ∫ u : ℝ, f u *
          Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam) :=
            C_intrinsicEntire_pointwiseBochner lam alpha hlam ha f z
      _ = ∫ u : ℝ, g u *
            Complex.exp (Complex.I * z * (u : ℂ) / 2)
            ∂(Ultraspherical.measure lam) := h z
      _ = GaussianArea.entireRepresentative alpha
          (C_intrinsicEntire lam alpha hlam ha g) z :=
            (C_intrinsicEntire_pointwiseBochner lam alpha hlam ha g z).symm
  have hout :
      C_intrinsicEntire lam alpha hlam ha f =
      C_intrinsicEntire lam alpha hlam ha g :=
    GaussianArea.entireRepresentative_injective alpha hrepresentatives
  exact C_intrinsicEntire_injective lam alpha hlam ha hout

/-- Even when the outputs use DIFFERENT positive Gaussian weights,
equality of their canonical entire functions pointwise determines
equality of the original ultraspherical inputs. -/
theorem ultraspherical_crossAlpha_entireOutput_injective
    (lam alpha beta : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (hb : 0 < beta)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ z : ℂ,
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) z =
      GaussianArea.entireRepresentative beta
        (C_intrinsicEntire lam beta hlam hb g) z) :
    f = g := by
  have hsame :
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) =
      GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha g) := by
    funext z
    calc
      GaussianArea.entireRepresentative alpha
          (C_intrinsicEntire lam alpha hlam ha f) z =
        GaussianArea.entireRepresentative beta
          (C_intrinsicEntire lam beta hlam hb g) z := h z
      _ = GaussianArea.entireRepresentative alpha
          (C_intrinsicEntire lam alpha hlam ha g) z :=
            (C_intrinsicEntire_pointwise_independent_of_alpha
              lam alpha beta hlam ha hb g z).symm
  apply C_intrinsicEntire_injective lam alpha hlam ha
  exact GaussianArea.entireRepresentative_injective alpha hsame

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_crossAlpha_entireOutput_injective

end GegenbauerFock.GeneralUltrasphericalFock
