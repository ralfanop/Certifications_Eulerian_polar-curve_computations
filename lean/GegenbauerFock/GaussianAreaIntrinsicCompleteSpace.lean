import GegenbauerFock.GaussianAreaFullFockClosedPolynomialDensity

/-!
# V007 — complete intrinsic holomorphic Gaussian L² from certified closedness

The independently defined submodule of Gaussian L² classes admitting
an entire representative is closed by the previously Lean-certified
analytic proof. This bridge exposes closedness for a locally generated
CompleteSpace instance when the Gaussian parameter is positive. No
extra closedness hypothesis or axiom is introduced.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Certified intrinsic Gaussian-Fock closedness, reformulated for
local complete-space construction in the true Hilbert adjoint. -/
theorem intrinsicEntire_isClosed
    (alpha : ℝ) (ha : 0 < alpha) :
    IsClosed ((entireGaussianL2Submodule alpha :
      Submodule ℂ (Lp ℂ 2 (gaussianAreaMeasure alpha))) : Set
      (Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  exact entireGaussianL2Submodule_isClosed alpha ha

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_isClosed

end GegenbauerFock.GaussianArea
