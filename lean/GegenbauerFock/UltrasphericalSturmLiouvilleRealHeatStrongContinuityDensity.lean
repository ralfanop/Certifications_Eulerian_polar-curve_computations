import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# V007 — C₀ continuity at time zero from contraction and dense-mode continuity

A bounded-operator family H_s on a real normed space, s≥0, is assumed
uniformly contractive. If for a dense family D its orbits approach each
d∈D as s tends to zero through nonnegative times, then the same
strong continuity at zero holds for EVERY vector.

The proof is an explicit ε/4 argument using the norm contraction
estimate and density. It applies later to the true weighted-real-L²
limiting Yosida semigroup, once continuity of its normalized Gegenbauer
modes has been certified.
-/

noncomputable section
namespace GegenbauerFock.Ultraspherical

open Filter
open scoped Topology

/-- Uniform contraction and strong continuity at time zero on a
dense set imply strong C₀ continuity at zero on all vectors. -/
theorem strongContinuityAtZero_of_contractions_on_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : ℝ → E →L[ℝ] E)
    (hcontract : ∀ s : ℝ, 0 ≤ s → ‖S s‖ ≤ 1)
    (D : Set E) (hD : Dense D)
    (hcont : ∀ d ∈ D,
      Tendsto (fun s : ℝ => S s d) (𝓝[≥] (0 : ℝ)) (𝓝 d))
    (f : E) :
    Tendsto (fun s : ℝ => S s f) (𝓝[≥] (0 : ℝ)) (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro eps heps
  obtain ⟨d, hd, hfd⟩ :=
    hD.exists_dist_lt f (show 0 < eps / 4 by positivity)
  have hclose :
      ∀ᶠ s : ℝ in 𝓝[≥] (0 : ℝ),
        dist (S s d) d < eps / 2 :=
    (Metric.tendsto_nhds.mp (hcont d hd)) (eps / 2) (by positivity)
  have hpositive : ∀ᶠ s : ℝ in 𝓝[≥] (0 : ℝ), 0 ≤ s := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hs
  filter_upwards [hpositive, hclose] with s hs hsd
  have hbound : dist (S s f) (S s d) ≤ dist f d := by
    rw [dist_eq_norm, ← map_sub, dist_eq_norm]
    calc
      ‖S s (f - d)‖ ≤ ‖S s‖ * ‖f - d‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖f - d‖ :=
        mul_le_mul_of_nonneg_right (hcontract s hs) (norm_nonneg _)
      _ = ‖f - d‖ := one_mul _
  have htriangle : dist (S s d) f ≤
      dist (S s d) d + dist d f := dist_triangle _ _ _
  calc
    dist (S s f) f ≤ dist (S s f) (S s d) + dist (S s d) f :=
      dist_triangle _ _ _
    _ ≤ dist (S s f) (S s d) +
        (dist (S s d) d + dist d f) := by linarith
    _ < eps := by
      rw [dist_comm d f]
      linarith

#print axioms GegenbauerFock.Ultraspherical.strongContinuityAtZero_of_contractions_on_dense

end GegenbauerFock.Ultraspherical
