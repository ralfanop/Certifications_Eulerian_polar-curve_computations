import GegenbauerFock.GegenbauerIntrinsicEntireFourierUniformForwardContinuity
import GegenbauerFock.GegenbauerIntrinsicEntireFourierSampleRangeEquiv

/-!
# V007 — a closed-graph Fourier inverse that is nowhere continuous

For any bounded identifying complex-frequency sampling set, the
actual Fourier–Bochner sampling operator is continuous and injective.
Its inverse on the exact range is nowhere continuous, although the
inverse graph IS CLOSED in the product of the uniform-data range
topology and the ultraspherical source L² topology.

The closed-graph theorem does not apply to the inverse in this
setting because its data domain is the (generally incomplete) true
range, not a complete Banach data space. This module certifies the
closedness directly and does not assume completeness of that range.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For bounded sampled frequencies, the graph of the exact inverse
to the actual Fourier–Bochner map, taken in the topology of uniform
observations times the source Hilbert topology, is CLOSED.

This does not assert continuity of the inverse. -/
theorem ultraspherical_fourierBochner_canonicalSampleInverse_graph_closed
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    IsClosed {p :
        Set.range (ultraspherical_fourierBochner_uniformSamples lam S) ×
          Lp ℂ 2 (Ultraspherical.measure lam) |
      ultraspherical_fourierBochner_canonicalSampleInverse lam S p.1 = p.2} := by
  let F := ultraspherical_fourierBochner_uniformSamples lam S
  let r := ultraspherical_fourierBochner_canonicalSampleInverse lam S
  have hF : Continuous F :=
    ultraspherical_fourierBochner_uniformSamples_continuous
      lam alpha hlam ha S R hR hbound
  have hrange :
      ∀ d : Set.range F, F (r d) = (d : UniformFun S ℂ) := by
    intro d
    have h := congrArg Subtype.val
      (ultraspherical_fourierBochner_canonicalSampleInverse_right lam S d)
    exact h
  have hgraph_eq :
      {p : Set.range F × Lp ℂ 2 (Ultraspherical.measure lam) |
        r p.1 = p.2} =
      {p : Set.range F × Lp ℂ 2 (Ultraspherical.measure lam) |
        F p.2 = (p.1 : UniformFun S ℂ)} := by
    ext p
    constructor
    · intro hp
      have h := hrange p.1
      rw [hp] at h
      exact h
    · intro hp
      have heq :
          (⟨F p.2, ⟨p.2, rfl⟩⟩ : Set.range F) = p.1 :=
        Subtype.ext hp
      rw [← heq]
      exact ultraspherical_fourierBochner_canonicalSampleInverse_left
        lam alpha hlam ha S w hacc p.2
  change IsClosed {p : Set.range F × Lp ℂ 2 (Ultraspherical.measure lam) |
    r p.1 = p.2}
  rw [hgraph_eq]
  have hleft : Continuous
      (fun p : Set.range F × Lp ℂ 2 (Ultraspherical.measure lam) =>
        F p.2) :=
    hF.comp continuous_snd
  have hright : Continuous
      (fun p : Set.range F × Lp ℂ 2 (Ultraspherical.measure lam) =>
        (p.1 : UniformFun S ℂ)) :=
    continuous_subtype_val.comp continuous_fst
  exact isClosed_eq hleft hright

/-- The exact Fourier inverse has a closed graph while being
DISCONTINUOUS at every admissible datum, a concrete example of why
the completeness assumptions in closed-graph theorems matter. -/
theorem ultraspherical_fourierBochner_canonicalSampleInverse_closedGraph_nowhereContinuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    IsClosed {p :
        Set.range (ultraspherical_fourierBochner_uniformSamples lam S) ×
          Lp ℂ 2 (Ultraspherical.measure lam) |
      ultraspherical_fourierBochner_canonicalSampleInverse lam S p.1 = p.2} ∧
    (∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ¬ ContinuousAt
        (ultraspherical_fourierBochner_canonicalSampleInverse lam S) d) := by
  exact ⟨ultraspherical_fourierBochner_canonicalSampleInverse_graph_closed
      lam alpha hlam ha S w R hR hbound hacc,
    ultraspherical_fourierBochner_canonicalSampleInverse_nowhereContinuous
      lam alpha hlam ha S w R hR hbound hacc⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_canonicalSampleInverse_graph_closed
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_canonicalSampleInverse_closedGraph_nowhereContinuous

end GegenbauerFock.GeneralUltrasphericalFock
