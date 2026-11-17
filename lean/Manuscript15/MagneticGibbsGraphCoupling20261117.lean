import Manuscript15.Section27PrimalWasserstein

/-!
M15 §8.4: graph-coupling construction for a measurable transport map.
This constructs a genuine coupling of a law and its pushforward.
The identification of the particular magnetic Gibbs law and its
rounding map, including their moment and spectral estimates, remains open.
-/

open MeasureTheory
noncomputable section

namespace Manuscript15.MagneticGibbs.GraphCoupling
open Manuscript15.Section27.Primal

/-- The graph measure has exactly the required two marginals. -/
theorem graph_measure_coupling (μ : Measure ℝ) (T : ℝ → ℝ)
    (hT : Measurable T) :
    Measure.map (fun x : ℝ => (x, T x)) μ ∈
      couplings μ (Measure.map T μ) := by
  let g : ℝ → ℝ × ℝ := fun x => (x, T x)
  have hg : Measurable g := measurable_id.prodMk hT
  change Measure.map Prod.fst (Measure.map g μ) = μ ∧
    Measure.map Prod.snd (Measure.map g μ) = Measure.map T μ
  constructor
  · rw [Measure.map_map measurable_fst hg]
    simpa [g] using (Measure.map_id : Measure.map id μ = μ)
  · rw [Measure.map_map measurable_snd hg]
    rfl

end Manuscript15.MagneticGibbs.GraphCoupling

#print axioms Manuscript15.MagneticGibbs.GraphCoupling.graph_measure_coupling
