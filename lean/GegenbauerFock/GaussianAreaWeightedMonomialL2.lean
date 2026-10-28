import GegenbauerFock.GaussianAreaMonomialL2Integrability
import Mathlib.MeasureTheory.Function.L2Space

/-!
# V007 — concrete Gaussian weighted L² monomials

Define the genuine normalized Gaussian area measure on ℂ:
  dμ_α = (α / π) * exp(-α‖z‖²) dA(z).
For α > 0, prove every complex monomial belongs to L²(μ_α).

This goes beyond the scalar Gaussian Gram identities: the actual
weighted square norm is integrable and each monomial has a valid
MemLp membership proof. Constructing the Hilbert-valued embedding
and proving surjectivity onto *all* holomorphic Gaussian L²
functions are still separate obligations.
-/

noncomputable section

open MeasureTheory

namespace GegenbauerFock.GaussianArea

/-- The normalized positive Gaussian-area density, as an
ENNReal-valued Radon–Nikodym derivative with respect to volume. -/
noncomputable def gaussianAreaMeasure (alpha : ℝ) : Measure ℂ :=
  (volume : Measure ℂ).withDensity
    (fun z : ℂ => ENNReal.ofReal
      ((alpha / Real.pi) * Real.exp (-alpha * ‖z‖ ^ 2)))

/-- Positive-weight Gaussian Fock monomials genuinely belong
to the weighted L² space of the whole complex plane. -/
theorem monomial_memLp_two_gaussianArea
    (alpha : ℝ) (ha : 0 < alpha) (n : ℕ) :
    MemLp (fun z : ℂ => z ^ n) 2 (gaussianAreaMeasure alpha) := by
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
  have hbase : Integrable (fun z : ℂ =>
      (ENNReal.ofReal (rho z)).toReal • (‖z ^ n‖ ^ 2)) := by
    convert normalized_monomial_gaussian_norm_sq_integrable alpha ha n using 1
    funext z
    rw [ENNReal.toReal_ofReal (hnonneg z)]
    dsimp [rho]
    dsimp [SMul.smul]
    ring
  have hweighted :
      Integrable (fun z : ℂ => ‖z ^ n‖ ^ 2) (gaussianAreaMeasure alpha) := by
    change Integrable (fun z : ℂ => ‖z ^ n‖ ^ 2)
      ((volume : Measure ℂ).withDensity (fun z : ℂ => ENNReal.ofReal (rho z)))
    exact (integrable_withDensity_iff_integrable_smul' hrho_meas hrho_finite).2 hbase
  have hmeas : AEStronglyMeasurable (fun z : ℂ => z ^ n)
      (gaussianAreaMeasure alpha) := by
    fun_prop
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hweighted

#print axioms GegenbauerFock.GaussianArea.monomial_memLp_two_gaussianArea

end GegenbauerFock.GaussianArea
