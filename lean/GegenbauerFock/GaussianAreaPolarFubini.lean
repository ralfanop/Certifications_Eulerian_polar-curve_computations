import GegenbauerFock.GaussianAreaRadialCircleMomentUniqueness
import GegenbauerFock.GaussianAreaMixedPullbackIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# V007 — Fubini on the genuine complex polar chart

This module supplies the measure-theoretic Fubini step after the
Mathlib complex polar-coordinate change of variables. The integrability
hypothesis concerns the *actual Jacobian-weighted pullback*, not a
formal angular expression. It also specializes the result to the
already certified Gaussian mixed monomials.

The subsequent identification with Real.circleAverage for arbitrary
entire Gaussian L² representatives remains a separate obligation.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The actual planar complex integral is the iterated radial/angular
integral on Mathlib's open polar chart, provided its Jacobian-weighted
pullback is integrable. This is the full Bochner Fubini theorem, with
no unproved interchange of integrals. -/
theorem planar_integral_eq_iterated_polar
    (f : ℂ → ℂ)
    (hf : IntegrableOn
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) :
    (∫ z : ℂ, f z) =
      (∫ r in Set.Ioi (0 : ℝ),
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, theta))) := by
  have hprod : Integrable
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))).prod
        ((volume : Measure ℝ).restrict (Set.Ioo (-Real.pi) Real.pi))) := by
    change Integrable
      (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      ((volume : Measure (ℝ × ℝ)).restrict
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi)) at hf
    simpa only [Measure.volume_eq_prod, ← Measure.prod_restrict] using hf
  calc
    (∫ z : ℂ, f z) =
        (∫ p : ℝ × ℝ in Complex.polarCoord.target,
          p.1 • f (Complex.polarCoord.symm p)) :=
      (Complex.integral_comp_polarCoord_symm f).symm
    _ = (∫ p : ℝ × ℝ in
        Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • f (Complex.polarCoord.symm p)) := by
      rw [Complex.polarCoord_target]
    _ = (∫ r in Set.Ioi (0 : ℝ),
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          r • f (Complex.polarCoord.symm (r, theta))) := by
      simpa only [Measure.volume_eq_prod, ← Measure.prod_restrict] using
        (integral_prod
          (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
          hprod)

/-- Fubini for the genuine Gaussian mixed monomial planar moment,
without assuming any angular orthogonality or Taylor identity. -/
theorem gaussian_mixed_monomial_integral_eq_iterated_polar
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    (∫ z : ℂ,
      z ^ m * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ)) =
      (∫ r in Set.Ioi (0 : ℝ),
        ∫ theta in Set.Ioo (-Real.pi) Real.pi,
          r • ((Complex.polarCoord.symm (r, theta)) ^ m *
            star ((Complex.polarCoord.symm (r, theta)) ^ n) *
            (Real.exp
              (-alpha * ‖Complex.polarCoord.symm (r, theta)‖ ^ 2) : ℂ))) := by
  exact planar_integral_eq_iterated_polar
    (fun z : ℂ =>
      z ^ m * star (z ^ n) *
        (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))
    (polar_gaussian_mixed_pullback_integrable alpha ha m n)

#print axioms GegenbauerFock.GaussianArea.planar_integral_eq_iterated_polar
#print axioms GegenbauerFock.GaussianArea.gaussian_mixed_monomial_integral_eq_iterated_polar

end GegenbauerFock.GaussianArea
