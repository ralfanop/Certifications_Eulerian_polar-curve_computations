import GegenbauerFock.GaussianAreaPolarProductIntegrability

/-!
# V007 — integrable polar pullback of the actual Gaussian mixed monomial

The integrability certificate here is for the exact Jacobian-weighted
pullback of the complex-plane mixed monomial, not just its separable
radial-angular proxy. The proof uses the previously certified pointwise
polar factorization and genuine L¹ integrability of the radial-angular
product on Mathlib's open polar chart.

The change-of-variables transport of integrability all the way back
to the complex plane, and the onto Bargmann–Fock isometry, remain open.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The *actual* Jacobian-weighted Gaussian mixed monomial after the
complex polar change of coordinates is integrable on the true chart,
for all natural m,n and positive alpha. -/
theorem polar_gaussian_mixed_pullback_integrable
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    IntegrableOn
      (fun p : ℝ × ℝ =>
        p.1 • ((Complex.polarCoord.symm p) ^ m *
          star ((Complex.polarCoord.symm p) ^ n) *
          (Real.exp (-alpha * ‖Complex.polarCoord.symm p‖ ^ 2) : ℂ)))
      (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi) := by
  have h := polar_gaussian_mixed_product_integrable alpha ha m n
  refine h.congr_fun ?_ (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  exact (polar_gaussian_mixed_monomial_factorization alpha m n p hp).symm

#print axioms GegenbauerFock.GaussianArea.polar_gaussian_mixed_pullback_integrable

end GegenbauerFock.GaussianArea
