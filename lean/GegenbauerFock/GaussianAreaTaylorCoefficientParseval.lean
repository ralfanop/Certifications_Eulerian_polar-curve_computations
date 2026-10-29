import GegenbauerFock.GaussianAreaExplicitTaylorFourierSeries
import GegenbauerFock.GaussianAreaFullIntrinsicEvaluation

/-!
# V007 — the exact Taylor-derivative coefficient vector and Parseval norm

The intrinsic Gaussian Fock holomorphic class has a genuine `lp`
vector of normalized derivatives, not merely an unstructured sequence.
The full Gaussian coefficient analysis recovers this exact vector;
the isometric reconstruction provides a sharp norm identity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Genuine square-summable Taylor-derivative sequence of every entire
Gaussian L² class, normalized in the holomorphic Gaussian monomial basis. -/
noncomputable def intrinsicTaylorCoefficients
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    lp (fun _ : ℕ => ℂ) 2 :=
  ⟨fun n : ℕ =>
      monomialWeight alpha n *
        (((alpha ^ (-(n : ℝ)) : ℝ) : ℂ) *
          iteratedDeriv n (entireRepresentative alpha x) 0),
    intrinsicEntire_scaledTaylor_memℓp alpha ha x⟩

/-- The explicit normalized-derivative sequence *is exactly* the
Hilbert adjoint coefficient analysis of the true Gaussian L² vector. -/
theorem intrinsicTaylorCoefficients_eq_analysis
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    intrinsicTaylorCoefficients alpha ha x =
      coefficientAnalysisL2 alpha ha
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  apply Subtype.ext
  funext n
  exact (coefficientAnalysisL2_intrinsic_eq_scaled_taylor alpha ha x n).symm

/-- Full Parseval equality for the normalized Taylor-derivative vector,
with the actual intrinsic Gaussian L² norm and no error term. -/
theorem intrinsicTaylorCoefficients_norm_eq
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    ‖intrinsicTaylorCoefficients alpha ha x‖ = ‖x‖ := by
  rw [intrinsicTaylorCoefficients_eq_analysis alpha ha x]
  exact (intrinsicEntire_gaussian_parseval_norm alpha ha x).symm

/-- Polarized Parseval identity: the actual Gaussian Fock Hilbert
inner product equals the complex ℓ² inner product of the two
normalized Taylor-derivative coefficient vectors. -/
theorem intrinsicTaylorCoefficients_inner_eq
    (alpha : ℝ) (ha : 0 < alpha)
    (x y : entireGaussianL2Submodule alpha) :
    inner ℂ (intrinsicTaylorCoefficients alpha ha x)
      (intrinsicTaylorCoefficients alpha ha y) = inner ℂ x y := by
  rw [intrinsicTaylorCoefficients_eq_analysis alpha ha x,
    intrinsicTaylorCoefficients_eq_analysis alpha ha y]
  calc
    inner ℂ
        (coefficientAnalysisL2 alpha ha
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha)))
        (coefficientAnalysisL2 alpha ha
          (y : Lp ℂ 2 (gaussianAreaMeasure alpha))) =
      inner ℂ
        (coefficientSynthesisL2 alpha ha
          (coefficientAnalysisL2 alpha ha
            (x : Lp ℂ 2 (gaussianAreaMeasure alpha))))
        (coefficientSynthesisL2 alpha ha
          (coefficientAnalysisL2 alpha ha
            (y : Lp ℂ 2 (gaussianAreaMeasure alpha)))) :=
      ((coefficientSynthesisL2 alpha ha).inner_map_map _ _).symm
    _ = inner ℂ x y := by
      rw [coefficientSynthesis_analysis_eq_intrinsic alpha ha x,
        coefficientSynthesis_analysis_eq_intrinsic alpha ha y]
      rfl

#print axioms GegenbauerFock.GaussianArea.intrinsicTaylorCoefficients_inner_eq

#print axioms GegenbauerFock.GaussianArea.intrinsicTaylorCoefficients_eq_analysis
#print axioms GegenbauerFock.GaussianArea.intrinsicTaylorCoefficients_norm_eq

end GegenbauerFock.GaussianArea
