import GegenbauerFock.GegenbauerIntrinsicEntireFockOperator
import GegenbauerFock.GaussianAreaCoherentIntrinsicAgreement
import GegenbauerFock.EvaluationComposite
import GegenbauerFock.GaussianAreaFullIntrinsicEvaluation

/-!
# V007 — exact pointwise Fourier–Bochner formula in the full intrinsic Fock space

The coefficient-side ultraspherical integral identity had previously
been certified for each complex z. The independent entire-representative
Gaussian L² space has now been proved closed, polynomially dense, and
isometrically equivalent to the full coefficient Hilbert space.

We identify, pointwise at *all* complex frequencies, the canonical
entire representative of the TRUE intrinsic-Fock-valued ultraspherical
transform with its genuine complex Bochner Fourier integral.
This is not merely an L²-a.e. equality or an assertion about formal
coefficient series. Differentiability of the actual Fourier integral
follows without any assumption that the compact transform is onto.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The intrinsic Fock-valued transform is exactly the entire
coherent-state synthesis of the same genuine Gegenbauer coefficient
vector, as a Gaussian L² class with its analytic representative. -/
theorem C_intrinsicEntire_eq_synthesizedIntrinsicVector
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    C_intrinsicEntire lam alpha hlam ha f =
      GaussianArea.synthesizedIntrinsicVector alpha ha
        (C lam alpha hlam ha f) := by
  apply Subtype.ext
  rfl

/-- The UNIQUE analytic representative of the actual Gaussian
Fock L² output equals its Bochner Fourier integral for EVERY z∈ℂ.
No conversion of analytic a.e. equality into pointwise equality
is left unproved: canonical representatives are used throughout. -/
theorem C_intrinsicEntire_pointwiseBochner
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (z : ℂ) :
    GaussianArea.entireRepresentative alpha
      (C_intrinsicEntire lam alpha hlam ha f) z =
      ∫ u : ℝ, f u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam) := by
  calc
    GaussianArea.entireRepresentative alpha
        (C_intrinsicEntire lam alpha hlam ha f) z =
      GaussianArea.intrinsicEntireEvaluation alpha ha z
        (GaussianArea.synthesizedIntrinsicVector alpha ha
          (C lam alpha hlam ha f)) := by
            rw [C_intrinsicEntire_eq_synthesizedIntrinsicVector]
            rfl
    _ = FockEvaluation.evaluation alpha ha z
        (C lam alpha hlam ha f) :=
          GaussianArea.intrinsicEntireEvaluation_synthesized
            alpha ha (C lam alpha hlam ha f) z
    _ = ∫ u : ℝ, f u *
          Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam) := by
            change evaluatedOperator lam alpha hlam ha z f = _
            exact evaluatedOperator_eq_integral lam alpha hlam ha z f

/-- The genuine ultraspherical complex-frequency Fourier integral
is entire for every L² input. Its analytic structure comes from the
actual full intrinsic Gaussian Fock Hilbert-space realization. -/
theorem ultraspherical_fourierIntegral_differentiable_via_intrinsicFock
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    Differentiable ℂ (fun z : ℂ =>
      ∫ u : ℝ, f u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam)) := by
  have hfunctions :
      (fun z : ℂ =>
        ∫ u : ℝ, f u *
          Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
        GaussianArea.entireRepresentative alpha
          (C_intrinsicEntire lam alpha hlam ha f) := by
    funext z
    exact (C_intrinsicEntire_pointwiseBochner lam alpha hlam ha f z).symm
  rw [hfunctions]
  exact GaussianArea.entireRepresentative_differentiable alpha
    (C_intrinsicEntire lam alpha hlam ha f)

/-- Analytic point evaluation of the genuine Fourier integral is
controlled by the Fock reproducing-functional norm and the actual
coefficient-space transform norm. -/
theorem intrinsicEntire_fourierIntegral_evaluation_bound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) (z : ℂ) :
    ‖∫ u : ℝ, f u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam)‖ ≤
      ‖FockEvaluation.evaluation alpha ha z‖ *
        ‖C lam alpha hlam ha f‖ := by
  rw [← C_intrinsicEntire_pointwiseBochner lam alpha hlam ha f z]
  change ‖GaussianArea.intrinsicEntireEvaluation alpha ha z
      (C_intrinsicEntire lam alpha hlam ha f)‖ ≤ _
  simpa only [C_intrinsicEntire_norm] using
    (GaussianArea.intrinsicEntireEvaluation_norm_le_full
      alpha ha (C_intrinsicEntire lam alpha hlam ha f) z)

#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_eq_synthesizedIntrinsicVector
#print axioms GegenbauerFock.GeneralUltrasphericalFock.C_intrinsicEntire_pointwiseBochner
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierIntegral_differentiable_via_intrinsicFock
#print axioms GegenbauerFock.GeneralUltrasphericalFock.intrinsicEntire_fourierIntegral_evaluation_bound

end GegenbauerFock.GeneralUltrasphericalFock
