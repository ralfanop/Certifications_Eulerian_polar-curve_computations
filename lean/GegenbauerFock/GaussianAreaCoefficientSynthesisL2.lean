import GegenbauerFock.GaussianAreaTrueL2OrthonormalFamily
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# V007 — isometric coefficient synthesis into genuine Gaussian L²

The actual normalized complex monomials form an orthonormal family
in the completed Gaussian weighted L²(ℂ). The canonical Hilbert-sum
isometry synthesizes a square-summable coefficient vector into an
actual L² Gaussian vector, not a formal sequence of Gram entries.

The range is the closure of the polynomial span; equality of this
closed range with the complete holomorphic Gaussian L² subspace is
the remaining density/surjectivity obligation.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GegenbauerFock.GaussianArea

/-- Genuine isometric synthesis of arbitrary square-summable
Gaussian Fock coefficients into weighted complex L²(ℂ). -/
noncomputable def coefficientSynthesisL2
    (alpha : ℝ) (ha : 0 < alpha) :
    (lp (fun _ : ℕ => ℂ) 2) →ₗᵢ[ℂ]
      Lp ℂ 2 (gaussianAreaMeasure alpha) :=
  (orthonormal_normalizedMonomialL2Vector alpha ha).orthogonalFamily.linearIsometry

/-- The synthesis preserves the exact Hilbert norm of any infinite
square-summable sequence, without a finite-rank restriction. -/
theorem coefficientSynthesisL2_norm
    (alpha : ℝ) (ha : 0 < alpha)
    (a : lp (fun _ : ℕ => ℂ) 2) :
    ‖coefficientSynthesisL2 alpha ha a‖ = ‖a‖ :=
  (coefficientSynthesisL2 alpha ha).norm_map a

/-- Consequently the coefficient synthesis is injective on all ℓ². -/
theorem coefficientSynthesisL2_injective
    (alpha : ℝ) (ha : 0 < alpha) :
    Function.Injective (coefficientSynthesisL2 alpha ha) :=
  (coefficientSynthesisL2 alpha ha).injective

#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_norm
#print axioms GegenbauerFock.GaussianArea.coefficientSynthesisL2_injective

end GegenbauerFock.GaussianArea
