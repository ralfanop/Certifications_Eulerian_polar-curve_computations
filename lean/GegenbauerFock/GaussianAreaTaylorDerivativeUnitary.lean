import GegenbauerFock.GaussianAreaTaylorCoefficientParseval
import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GaussianAreaCoefficientAnalysisAdjoint

/-!
# V007 — explicit derivative-coordinate unitary for intrinsic Bargmann–Fock

The full intrinsic Gaussian Bargmann–Fock space was independently
proved isometrically isomorphic to complex square-summable sequences.
We now identify the inverse of that established unitary, at every
index, with the *actual normalized complex Taylor derivative*.

The equivalence is with intrinsically entire Gaussian L² functions,
not the entire ambient Gaussian L² space.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The complete intrinsic Gaussian Bargmann–Fock Hilbert space is
unitarily equivalent to the ℓ² space of normalized Taylor derivatives.
This is the inverse of the independently kernel-certified synthesis
unitary, so its linearity, inverse and exact norms are inherited. -/
noncomputable def intrinsicTaylorDerivativeUnitary
    (alpha : ℝ) (ha : 0 < alpha) :
    entireGaussianL2Submodule alpha ≃ₗᵢ[ℂ]
      lp (fun _ : ℕ => ℂ) 2 :=
  (coefficientIntrinsicEntireEquiv alpha ha).symm

/-- The abstract inverse of coefficient synthesis is literally the
Hilbert vector constructed from normalized analytic derivatives. -/
theorem intrinsicTaylorDerivativeUnitary_eq_coefficients
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    intrinsicTaylorDerivativeUnitary alpha ha x =
      intrinsicTaylorCoefficients alpha ha x := by
  obtain ⟨a, rfl⟩ :=
    coefficientSynthesisToIntrinsicEntire_surjective alpha ha x
  have hu :
      intrinsicTaylorDerivativeUnitary alpha ha
        (coefficientSynthesisToIntrinsicEntire alpha ha a) = a := by
    change (coefficientIntrinsicEntireEquiv alpha ha).symm
      ((coefficientIntrinsicEntireEquiv alpha ha) a) = a
    simp
  rw [hu, intrinsicTaylorCoefficients_eq_analysis]
  change a = coefficientAnalysisL2 alpha ha
    (coefficientSynthesisL2 alpha ha a)
  exact (coefficientAnalysisL2_synthesis alpha ha a).symm

/-- Coordinatewise closed-form derivative formula for the full
complex-linear isometric equivalence; no formal Taylor space
replaces the genuine Gaussian holomorphic L² Hilbert space. -/
theorem intrinsicTaylorDerivativeUnitary_apply
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    intrinsicTaylorDerivativeUnitary alpha ha x n =
      monomialWeight alpha n *
        (((alpha ^ (-(n : ℝ)) : ℝ) : ℂ) *
          iteratedDeriv n (entireRepresentative alpha x) 0) := by
  rw [intrinsicTaylorDerivativeUnitary_eq_coefficients alpha ha x]
  rfl

#print axioms GegenbauerFock.GaussianArea.intrinsicTaylorDerivativeUnitary
#print axioms GegenbauerFock.GaussianArea.intrinsicTaylorDerivativeUnitary_eq_coefficients
#print axioms GegenbauerFock.GaussianArea.intrinsicTaylorDerivativeUnitary_apply

end GegenbauerFock.GaussianArea
