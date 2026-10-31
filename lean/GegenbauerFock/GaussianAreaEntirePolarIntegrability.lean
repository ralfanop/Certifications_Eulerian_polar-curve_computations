import GegenbauerFock.GaussianAreaEntirePlanarL1
import GegenbauerFock.GaussianAreaPlanarIntegrabilityTransfer
import GegenbauerFock.GaussianAreaPolarAngularAlgebra

/-!
# V007 — integrability of entire Gaussian moments on the genuine polar chart

The reverse direction of the polar L¹ transfer is proved by the exact
lintegral identity, not by a formal use of Fubini.  The weighted entire
moments are continuous and have already been proved Lebesgue L¹.
This yields integrability of their actual Jacobian-weighted polar
pullbacks on the open Mathlib complex polar chart.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Every continuous planar L¹ function has an integrable Jacobian-weighted
pullback on the actual complex polar chart. -/
theorem polar_pullback_integrable_of_continuous
    (f : ℂ → ℂ) (hc : Continuous f)
    (hf : Integrable f (volume : Measure ℂ)) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  have hpolar : Continuous
      (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
    simp_rw [polarCoord_symm_eq_radius_exp]
    fun_prop
  have hcont : Continuous
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p)) :=
    continuous_fst.smul (hc.comp hpolar)
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  change
    (∫⁻ p : ℝ × ℝ in
      Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ‖p.1 • f (Complex.polarCoord.symm p)‖ₑ) < ⊤
  rw [← lintegral_enorm_eq_polar f]
  exact hf.2

/-- The exact normalized Gaussian density times an intrinsic entire
representative and any conjugate monomial has an integrable genuine
polar pullback, including the radial Jacobian. -/
theorem entireRepresentative_polar_weighted_moment_integrable
    (alpha : ℝ) (ha : 0 < alpha)
    (x : entireGaussianL2Submodule alpha) (n : ℕ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 •
          (((alpha / Real.pi) *
            Real.exp (-alpha * ‖Complex.polarCoord.symm p‖ ^ 2) : ℝ) •
            (entireRepresentative alpha x (Complex.polarCoord.symm p) *
              star ((Complex.polarCoord.symm p) ^ n))))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  have hrep : Continuous (entireRepresentative alpha x) :=
    (entireRepresentative_differentiable alpha x).continuous
  have hc : Continuous (fun z : ℂ =>
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n))) := by
    fun_prop
  exact polar_pullback_integrable_of_continuous
    (fun z : ℂ =>
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) •
        (entireRepresentative alpha x z * star (z ^ n)))
    hc (entireRepresentative_planar_weighted_moment_integrable alpha ha x n)

#print axioms GegenbauerFock.GaussianArea.polar_pullback_integrable_of_continuous
#print axioms GegenbauerFock.GaussianArea.entireRepresentative_polar_weighted_moment_integrable

end GegenbauerFock.GaussianArea
