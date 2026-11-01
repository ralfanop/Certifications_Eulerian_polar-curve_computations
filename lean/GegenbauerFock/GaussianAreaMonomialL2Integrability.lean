import GegenbauerFock.GaussianAreaPlanarIntegrabilityTransfer
import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# V007 — genuine Gaussian L² integrability of complex monomials

For α>0, the exact planar mixed-monomial integrability theorem
implies real Lebesgue integrability of each squared monomial norm
against exp(-α‖z‖²). This is a concrete L² prerequisite; it does
not yet construct a completed weighted holomorphic Fock space.

All statements use genuine complex-plane Lebesgue measure.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- A normalized mixed monomial belongs to L¹ of complex-plane
Lebesgue measure for all α>0 and natural m,n. -/
theorem normalized_gaussian_mixed_monomial_integrable
    (alpha : ℝ) (ha : 0 < alpha) (m n : ℕ) :
    Integrable (fun z : ℂ =>
      ((alpha / Real.pi : ℝ) : ℂ) *
        (z ^ m * star (z ^ n) *
          (Real.exp (-alpha * ‖z‖ ^ 2) : ℂ))) := by
  exact (gaussian_mixed_monomial_integrable alpha ha m n).const_mul _

/-- The real squared-norm Gaussian density is an integrable
function on the full two-dimensional complex plane. -/
theorem monomial_gaussian_norm_sq_integrable
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    Integrable (fun z : ℂ =>
      ‖z ^ n‖ ^ 2 * Real.exp (-alpha * ‖z‖ ^ 2)) := by
  have h := gaussian_mixed_monomial_integrable alpha ha n n
  have hc : Integrable (fun z : ℂ =>
      ((‖z ^ n‖ ^ 2 * Real.exp (-alpha * ‖z‖ ^ 2) : ℝ) : ℂ)) := by
    convert h using 1
    funext z
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  exact (Integrable.iff_ofReal (𝕜 := ℂ)).mpr hc

/-- Real L¹ of the squared monomial norm also holds under the
usual normalized positive Gaussian-area density. -/
theorem normalized_monomial_gaussian_norm_sq_integrable
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    Integrable (fun z : ℂ =>
      (alpha / Real.pi) *
        (‖z ^ n‖ ^ 2 * Real.exp (-alpha * ‖z‖ ^ 2))) := by
  exact (monomial_gaussian_norm_sq_integrable alpha ha n).const_mul _

#print axioms GegenbauerFock.GaussianArea.normalized_gaussian_mixed_monomial_integrable
#print axioms GegenbauerFock.GaussianArea.monomial_gaussian_norm_sq_integrable
#print axioms GegenbauerFock.GaussianArea.normalized_monomial_gaussian_norm_sq_integrable

end GegenbauerFock.GaussianArea
