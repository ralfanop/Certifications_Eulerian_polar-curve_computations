import GegenbauerFock.GaussianAreaFullIntrinsicFockSurjectivity
import GegenbauerFock.GaussianAreaReproducingCriterion
import GegenbauerFock.GaussianAreaPolynomialProjector

/-!
# V007 — unconditional reproducing identity for intrinsic Gaussian Fock vectors

The full intrinsic entire-representative Gaussian L² submodule is now
proved equal to the closed normalized-holomorphic-polynomial span.
This discharges the exact reproducing criterion previously established
without assuming polynomial density.

The result holds at every complex point for every intrinsically entire
weighted L² class, not merely for finite polynomials or abstract ℓ².
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The canonical orthogonal projector onto the Gaussian holomorphic
polynomial closure fixes every *intrinsic entire* Gaussian L² class. -/
theorem gaussianPolynomialProjector_fixes_intrinsicEntire
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) :
    gaussianPolynomialProjector alpha ha
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) =
      (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  exact (gaussianPolynomialProjector_eq_self_iff alpha ha _).2
    (intrinsicEntire_le_polynomialClosure_unconditional alpha ha x.property)

/-- The exact Gaussian coherent-state reproducing formula holds for
EVERY independently defined entire Gaussian L² representative. -/
theorem intrinsicEntireEvaluation_eq_projected_full
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (z : ℂ) :
    intrinsicEntireEvaluation alpha ha z x =
      projectedGaussianEvaluation alpha ha z
        (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  exact (intrinsicEntire_le_polynomialClosure_iff_reproducing alpha ha).1
    (intrinsicEntire_le_polynomialClosure_unconditional alpha ha) x z

/-- The reproducing identity is valid simultaneously for all intrinsic
entire Fock vectors and all points of the complex plane. -/
theorem intrinsicEntire_reproducing_universal
    (alpha : ℝ) (ha : 0 < alpha) :
    ∀ x : entireGaussianL2Submodule alpha, ∀ z : ℂ,
      intrinsicEntireEvaluation alpha ha z x =
        projectedGaussianEvaluation alpha ha z
          (x : Lp ℂ 2 (gaussianAreaMeasure alpha)) := by
  exact (intrinsicEntire_le_polynomialClosure_iff_reproducing alpha ha).1
    (intrinsicEntire_le_polynomialClosure_unconditional alpha ha)

#print axioms GegenbauerFock.GaussianArea.gaussianPolynomialProjector_fixes_intrinsicEntire
#print axioms GegenbauerFock.GaussianArea.intrinsicEntireEvaluation_eq_projected_full
#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_reproducing_universal

end GegenbauerFock.GaussianArea
