import GegenbauerFock.UltrasphericalSturmLiouvilleActualMoments

/-!
# V007 — integrability of every genuine ultraspherical real monomial

This is an analytic bridge for identifying the finite Green moment
matrix with actual integrals of polynomial evaluations.

No self-adjoint extension or unbounded operator domain is asserted.
-/

noncomputable section
open MeasureTheory

namespace GegenbauerFock.Ultraspherical

/-- Every real monomial is integrable for the ACTUAL symmetric
Beta-pushforward ultraspherical probability law, for λ > 0. -/
theorem sturmMoment_monomial_integrable (lam : ℝ) (hlam : 0 < lam)
    (n : ℕ) :
    Integrable (fun u : ℝ => u ^ n) (measure lam) := by
  letI : IsProbabilityMeasure (measure lam) := probability lam hlam
  have hcontinuous : Continuous (fun u : ℝ => u ^ n) := by
    fun_prop
  apply Integrable.of_bound hcontinuous.aestronglyMeasurable 1
  filter_upwards [ae_mem_unit_interval lam] with u hu
  have huabs : |u| ≤ 1 := abs_le.mpr ⟨hu.1, hu.2⟩
  calc
    ‖u ^ n‖ = |u| ^ n := by simp
    _ ≤ (1 : ℝ) ^ n := by gcongr
    _ = 1 := by simp

/-- The constant moment is the exact normalization of the genuine
ultraspherical probability measure. -/
theorem sturmMoment_zero (lam : ℝ) (hlam : 0 < lam) :
    sturmMoment lam 0 = 1 := by
  change (∫ _u : ℝ, (1 : ℝ) ∂(measure lam)) = 1
  exact integral_one lam hlam

/-- The integral of an arbitrary real monomial equals its genuine,
already-defined sturmMoment without an assumed moment functional. -/
theorem sturmMoment_integral (lam : ℝ) (n : ℕ) :
    (∫ u : ℝ, u ^ n ∂(measure lam)) = sturmMoment lam n := rfl

#print axioms GegenbauerFock.Ultraspherical.sturmMoment_monomial_integrable
#print axioms GegenbauerFock.Ultraspherical.sturmMoment_zero
#print axioms GegenbauerFock.Ultraspherical.sturmMoment_integral

end GegenbauerFock.Ultraspherical
