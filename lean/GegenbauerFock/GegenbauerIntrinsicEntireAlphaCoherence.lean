import GegenbauerFock.GegenbauerIntrinsicEntireBochnerEvaluation

/-!
# V007 — independence of the entire Fourier–Bochner function from Gaussian Fock scale

For alpha,beta>0 the Gegenbauer transform is realized in distinct
intrinsic Gaussian entire-L² Hilbert spaces, with different weighted
norms. The two resulting canonical entire representatives nevertheless
coincide at EVERY complex point: they are the same actual Bochner Fourier
integral of the same ultraspherical source function.

This is an exact pointwise functional identity; it does not identify
the two Gaussian measures or the two Hilbert-space norms.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Changing the positive Fock scale parameter does not alter the
pointwise entire output: it alters only the Gaussian Hilbert norm. -/
theorem C_intrinsicEntire_pointwise_independent_of_alpha
    (lam alpha beta : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (hb : 0 < beta)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (z : ℂ) :
    GaussianArea.entireRepresentative alpha
      (C_intrinsicEntire lam alpha hlam ha f) z =
    GaussianArea.entireRepresentative beta
      (C_intrinsicEntire lam beta hlam hb f) z := by
  calc
    GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) z =
      ∫ u : ℝ, f u * Complex.exp
        (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam) :=
          C_intrinsicEntire_pointwiseBochner lam alpha hlam ha f z
    _ = GaussianArea.entireRepresentative beta
          (C_intrinsicEntire lam beta hlam hb f) z :=
          (C_intrinsicEntire_pointwiseBochner lam beta hlam hb f z).symm

/-- The canonical entire functions are literally equal as functions,
even though the two Gaussian-Fock output Hilbert spaces differ. -/
theorem C_intrinsicEntire_entireFunction_independent_of_alpha
    (lam alpha beta : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (hb : 0 < beta)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    GaussianArea.entireRepresentative alpha
      (C_intrinsicEntire lam alpha hlam ha f) =
    GaussianArea.entireRepresentative beta
      (C_intrinsicEntire lam beta hlam hb f) := by
  funext z
  exact C_intrinsicEntire_pointwise_independent_of_alpha
    lam alpha beta hlam ha hb f z

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_pointwise_independent_of_alpha
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_entireFunction_independent_of_alpha

end GegenbauerFock.GeneralUltrasphericalFock
