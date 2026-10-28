import GegenbauerFock.GaussianAreaNormalizedMonomialGram
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# V007 — Gaussian radial integrability on the genuine complex polar chart

For alpha > 0 and natural degrees m,n the radial part of the
Jacobian-weighted mixed Gaussian monomial has finite absolute
Lebesgue integral on (0,+infinity).

This is an integrability statement (not merely a value assigned by
the Bochner integral). It is the first required step toward a
genuine Gaussian L2 Gram construction, and does not assert the
full complex-plane L2 isometry or its surjectivity.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The real radial Jacobian-weighted Gaussian monomial profile
is genuinely Lebesgue integrable for alpha > 0. -/
theorem radial_gaussian_integrable_real
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    IntegrableOn
      (fun r : ℝ => r ^ (((m + n + 1 : ℕ) : ℝ)) *
        Real.exp (-alpha * r ^ 2)) (Set.Ioi 0) := by
  have hs : (-1 : ℝ) < (((m + n + 1 : ℕ) : ℝ)) := by
    positivity
  exact integrableOn_rpow_mul_exp_neg_mul_sq ha hs

/-- The corresponding complex-valued radial factor in the exact
polar decomposition is genuinely integrable on the positive ray. -/
theorem radial_gaussian_integrable_complex
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    IntegrableOn
      (fun r : ℝ => (r : ℂ) ^ (m + n + 1) *
        (Real.exp (-alpha * r ^ 2) : ℂ)) (Set.Ioi 0) := by
  have hreal := radial_gaussian_integrable_real alpha ha m n
  have hcomplex : IntegrableOn
      (fun r : ℝ =>
        ((r ^ (((m + n + 1 : ℕ) : ℝ)) *
          Real.exp (-alpha * r ^ 2) : ℝ) : ℂ)) (Set.Ioi 0) :=
    hreal.ofReal
  refine hcomplex.congr_fun ?_ measurableSet_Ioi
  intro r hr
  simp only [Real.rpow_natCast, Complex.ofReal_mul, Complex.ofReal_pow]

#print axioms GegenbauerFock.GaussianArea.radial_gaussian_integrable_real
#print axioms GegenbauerFock.GaussianArea.radial_gaussian_integrable_complex

end GegenbauerFock.GaussianArea
