import GegenbauerFock.GaussianAreaEntireMomentIntegrability

/-!
# V007 — transport Gaussian L¹ moments to actual planar Lebesgue L¹

The normalized Gaussian measure is the actual positive withDensity
measure on the complex plane. Its L¹ functions have a genuinely
Lebesgue-integrable density-weighted representative. In particular
this applies to every conjugate-monomial moment of an intrinsic entire
Gaussian L² vector. This proves the planar L¹ prerequisite for polar
Fubini, without yet claiming an angular circle-average identity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Weighted L¹ under the true Gaussian measure transfers to
ordinary planar L¹ after multiplying by its exact normalized density. -/
theorem gaussianArea_integrable_weighted_volume
    (alpha : ℝ) (ha : 0 < alpha) (f : ℂ → ℂ)
    (hf : Integrable f (gaussianAreaMeasure alpha)) :
    Integrable (fun z : ℂ =>
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) • f z)
      (volume : Measure ℂ) := by
  let rho : ℂ → ℝ :=
    fun z => (alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2)
  have hnonneg (z : ℂ) : 0 ≤ rho z := by
    dsimp [rho]
    positivity
  have hrho_meas : Measurable (fun z : ℂ => ENNReal.ofReal (rho z)) := by
    fun_prop
  have hrho_finite :
      ∀ᵐ z : ℂ ∂(volume : Measure ℂ),
        ENNReal.ofReal (rho z) < ⊤ := by
    filter_upwards [] with z
    simp
  have hweighted :
      Integrable (fun z : ℂ => (ENNReal.ofReal (rho z)).toReal • f z)
        (volume : Measure ℂ) := by
    change Integrable f
      ((volume : Measure ℂ).withDensity
        (fun z : ℂ => ENNReal.ofReal (rho z))) at hf
    exact (integrable_withDensity_iff_integrable_smul'
      hrho_meas hrho_finite).1 hf
  change Integrable (fun z : ℂ => rho z • f z) (volume : Measure ℂ)
  convert hweighted using 1
  funext z
  rw [ENNReal.toReal_ofReal (hnonneg z)]

/-- The exact normalized planar Gaussian density times an intrinsic
entire representative and any conjugate monomial is Lebesgue L¹. -/
theorem entireRepresentative_planar_weighted_moment_integrable
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    Integrable (fun z : ℂ =>
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n)))
      (volume : Measure ℂ) := by
  exact gaussianArea_integrable_weighted_volume alpha ha
    (fun z : ℂ => entireRepresentative alpha x z * star (z ^ n))
    (entireRepresentative_conjugate_monomial_integrable alpha ha x n)

#print axioms GegenbauerFock.GaussianArea.gaussianArea_integrable_weighted_volume
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_planar_weighted_moment_integrable

end GegenbauerFock.GaussianArea
