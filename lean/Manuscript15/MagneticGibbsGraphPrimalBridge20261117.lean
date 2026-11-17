import Manuscript15.MagneticGibbsGraphCoupling20261117
import Manuscript15.MagneticGibbsTransport20261116

/-!
M15 §8.4: compose the verified graph coupling with the primal
attainment theorem. This is a conditional bridge, NOT a proof that
the actual magnetic Gibbs laws satisfy its analytic hypotheses.
-/

open MeasureTheory
noncomputable section

namespace Manuscript15.MagneticGibbs.GraphPrimalBridge
open Manuscript15.Section27.Primal

/-- For a measurable map, the graph measure attains the primal infimum
provided the integrability, universal lower bound and graph equality
have been established for the actual cost. -/
theorem graph_primal_infimum
    (μ : Measure ℝ) (T : ℝ → ℝ) (hT : Measurable T)
    (c : ℝ × ℝ → ℝ) (m : ℝ → ℝ)
    (hm : Integrable m μ)
    (hc : ∀ γ ∈ couplings μ (Measure.map T μ), Integrable c γ)
    (hbelow : ∀ γ ∈ couplings μ (Measure.map T μ),
      ∀ᵐ p ∂γ, m p.1 ≤ c p)
    (heq : ∀ᵐ p ∂(Measure.map (fun x : ℝ => (x, T x)) μ),
      c p = m p.1) :
    sInf ((fun γ : Measure (ℝ × ℝ) => ∫ p, c p ∂γ) ''
      couplings μ (Measure.map T μ)) = ∫ x, m x ∂μ := by
  exact Manuscript15.MagneticGibbs.primal_infimum_of_attainment
    μ (Measure.map T μ) c m
    (Measure.map (fun x : ℝ => (x, T x)) μ)
    (Manuscript15.MagneticGibbs.GraphCoupling.graph_measure_coupling μ T hT)
    hm hc hbelow heq

end Manuscript15.MagneticGibbs.GraphPrimalBridge

#print axioms Manuscript15.MagneticGibbs.GraphPrimalBridge.graph_primal_infimum
