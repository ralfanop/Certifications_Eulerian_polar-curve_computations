import GegenbauerFock.GaussianAreaEntireDensityByMoments

/-!
# V007 — closedness of the intrinsic entire Gaussian L² submodule

The independently defined submodule of Gaussian L² classes admitting
an entire representative equals the closed polynomial span. Consequently
it is a closed subset of ambient L². This supplies a genuine
complete-space instance *locally* wherever a positive Gaussian parameter
is assumed; no global assumption or extra axiom of closedness is made.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The actual entire-representative submodule is closed inside planar
Gaussian L², by the unconditional analytic polynomial-density theorem. -/
theorem intrinsicEntire_isClosed
    (alpha : ℝ) (ha : 0 < alpha) :
    IsClosed ((entireGaussianL2Submodule alpha :
      Submodule ℂ (Lp ℂ 2 (gaussianAreaMeasure alpha))) : Set
      (Lp ℂ 2 (gaussianAreaMeasure alpha))) := by
  rw [intrinsicEntire_eq_gaussianPolynomialClosure alpha ha]
  unfold gaussianPolynomialClosure
  exact Submodule.isClosed_topologicalClosure _

#print axioms GegenbauerFock.GaussianArea.intrinsicEntire_isClosed

end GegenbauerFock.GaussianArea
