import GegenbauerFock.GaussianAreaMixedPullbackIntegrability

/-!
# V007 — transport genuine Gaussian L¹ integrability to the complex plane

The pinned Mathlib complex polar lintegral change of variables holds
even for nonintegrable functions. Applying it to the extended norm
and using the positivity of the radial coordinate transfers genuine
L¹ integrability of the Jacobian-weighted pullback to L¹(ℂ).

The specific Gaussian mixed monomial is continuous, and its polar
pullback has previously been proved integrable for α>0.
This establishes the finite absolute complex-plane integrals needed
for constructing Gaussian L² monomials.

The full holomorphic Gaussian Bargmann–Fock isometry and surjectivity
remain separate obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Norm-based polar substitution for arbitrary complex-valued
functions, using the true two-dimensional Lebesgue volume. -/
theorem lintegral_enorm_eq_polar (f : ℂ → ℂ) :
    (∫⁻ z : ℂ, ‖f z‖ₑ) =
      (∫⁻ p : ℝ × ℝ in
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) := by
  calc
    (∫⁻ z : ℂ, ‖f z‖ₑ) =
      (∫⁻ p : ℝ × ℝ in Complex.polarCoord.target,
        ENNReal.ofReal p.1 • ‖f (Complex.polarCoord.symm p)‖ₑ) :=
      (Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)).symm
    _ = (∫⁻ p : ℝ × ℝ in
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) := by
      rw [Complex.polarCoord_target]
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      simp only [smul_eq_mul, enorm_smul, Real.enorm_eq_ofReal hp.1.le]

/-- Integrability on the actual complex plane follows from
a.e. strong measurability and integrability of the polar pullback. -/
theorem integrable_of_polar_pullback_integrable
    (f : ℂ → ℂ)
    (hf : AEStronglyMeasurable f (volume : Measure ℂ))
    (hpolar : IntegrableOn
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) :
    Integrable f (volume : Measure ℂ) := by
  refine ⟨hf, ?_⟩
  change (∫⁻ z : ℂ, ‖f z‖ₑ) < ∞
  rw [lintegral_enorm_eq_polar f]
  exact hpolar.2

/-- Unconditional L¹ integrability of the full mixed monomial
against the genuine two-dimensional Gaussian weight, for α>0. -/
theorem gaussian_mixed_monomial_integrable
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    Integrable (fun z : ℂ =>
      z ^ m * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) := by
  apply integrable_of_polar_pullback_integrable
    (fun z : ℂ =>
      z ^ m * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))
  · have hc : Continuous (fun z : ℂ =>
        z ^ m * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) := by
      fun_prop
    exact hc.aestronglyMeasurable
  · exact polar_gaussian_mixed_pullback_integrable alpha ha m n

#print axioms GegenbauerFock.GaussianArea.lintegral_enorm_eq_polar
#print axioms GegenbauerFock.GaussianArea.integrable_of_polar_pullback_integrable
#print axioms GegenbauerFock.GaussianArea.gaussian_mixed_monomial_integrable

end GegenbauerFock.GaussianArea
