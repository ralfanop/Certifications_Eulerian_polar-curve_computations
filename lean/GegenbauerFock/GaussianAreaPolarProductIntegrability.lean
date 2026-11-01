import GegenbauerFock.GaussianAreaRadialIntegrability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# V007 — genuine integrability of the complex Gaussian polar product

For alpha > 0, the Jacobian-weighted Gaussian mixed-monomial
polar profile belongs to L¹ on the true open complex polar chart.
The proof uses integrability of the radial Gaussian profile,
continuity and compact-interval integrability of the Fourier
angular factor, and the product-measure integrability theorem.

The eventual planar change-of-variables integrability and onto
holomorphic Bargmann–Fock isometry remain separate obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- Every integer angular Fourier mode is integrable on the finite
open angular support of the pinned complex polar chart. -/
theorem polar_angular_mode_integrable (k : ℤ) :
    IntegrableOn
      (fun theta : ℝ =>
        Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ)))
      (Set.Ioo (-Real.pi) Real.pi) := by
  have hc : Continuous (fun theta : ℝ =>
      Complex.exp (((k : ℂ) * Complex.I) * (theta : ℂ))) := by
    fun_prop
  exact (hc.integrableOn_Icc).mono_set (by
    intro theta htheta
    exact ⟨htheta.1.le, htheta.2.le⟩)

/-- The full Jacobian-weighted radial/angular Gaussian product is
complex-valued integrable for alpha > 0 and all monomial degrees. -/
theorem polar_gaussian_mixed_product_integrable
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        ((p.1 : ℂ) ^ (m + n + 1) *
          (Real.exp (-alpha * p.1 ^ 2) : ℂ)) *
          Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
            Complex.I) * (p.2 : ℂ)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  have hr := radial_gaussian_integrable_complex alpha ha m n
  have ht := polar_angular_mode_integrable ((m : ℤ) - (n : ℤ))
  change Integrable
    (fun p : ℝ × ℝ =>
      ((p.1 : ℂ) ^ (m + n + 1) *
        (Real.exp (-alpha * p.1 ^ 2) : ℂ)) *
        Complex.exp (((((m : ℤ) - (n : ℤ) : ℤ) : ℂ) *
          Complex.I) * (p.2 : ℂ)))
    ((volume : Measure (ℝ × ℝ)).restrict
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi))
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact hr.mul_prod ht

#print axioms GegenbauerFock.GaussianArea.polar_angular_mode_integrable
#print axioms GegenbauerFock.GaussianArea.polar_gaussian_mixed_product_integrable

end GegenbauerFock.GaussianArea
