import Manuscript15.Section27CouplingIntegral
import Manuscript15.Section27AbstractInfimumBridge

/-!
# Manuscript 15 §2.7 — measure-level cost infimum bridge

This combines the proved measure-level transport inequality with the
order-theoretic infimum bridge. Equalities identifying the two observable
integrals with prescribed marginal integrals are explicit assumptions,
not claims that marginal preservation has already been proved.
This does not assert equality with Mathlib's Wasserstein-1 distance.
-/

open MeasureTheory
noncomputable section

namespace Manuscript15.Section27

/-- A common difference of observable integrals is bounded by the infimum
of all admissible coupling costs, provided every witness realizes the same
two marginal observables. -/
theorem integral_lipschitz_admissible_cost_infimum
    {Ω α : Type*} [MeasurableSpace Ω]
    (admissible : Set α) (μ : α → Measure Ω)
    (x y : Ω → ℝ) (φ : ℝ → ℝ)
    (A B : ℝ) (K : ℝ)
    (hne : admissible.Nonempty)
    (hA : ∀ a ∈ admissible,
      (∫ ω, φ (x ω) ∂μ a) = A)
    (hB : ∀ a ∈ admissible,
      (∫ ω, φ (y ω) ∂μ a) = B)
    (hx : ∀ a ∈ admissible, Integrable (fun ω => φ (x ω)) (μ a))
    (hy : ∀ a ∈ admissible, Integrable (fun ω => φ (y ω)) (μ a))
    (hc : ∀ a ∈ admissible,
      Integrable (fun ω => K * |x ω - y ω|) (μ a))
    (hLip : ∀ u v : ℝ, |φ u - φ v| ≤ K * |u - v|) :
    |A - B| ≤ sInf ((fun a => ∫ ω, K * |x ω - y ω| ∂μ a) '' admissible) := by
  apply bound_le_witness_cost_infimum admissible
    (fun a => ∫ ω, K * |x ω - y ω| ∂μ a) |A - B| hne
  intro a ha
  have h := integral_transport_of_pointwise_bound (μ a)
    (fun ω => φ (x ω)) (fun ω => φ (y ω))
    (fun ω => K * |x ω - y ω|) (hx a ha) (hy a ha) (hc a ha)
    (fun ω => hLip (x ω) (y ω))
  rw [hA a ha, hB a ha] at h
  exact h

#print axioms Manuscript15.Section27.integral_lipschitz_admissible_cost_infimum

end Manuscript15.Section27
