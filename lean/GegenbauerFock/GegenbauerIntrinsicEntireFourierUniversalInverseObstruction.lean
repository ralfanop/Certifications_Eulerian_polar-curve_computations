import GegenbauerFock.GegenbauerIntrinsicEntireFourierInverseRigidity
import GegenbauerFock.GegenbauerIntrinsicEntireFourierInverseClosedGraph
import GegenbauerFock.GegenbauerIntrinsicEntireFourierUniformSamplingNoEmbedding

/-!
# Universal obstructions to continuous exact Fourier–Bochner reconstruction

The forward ultraspherical Fourier–Bochner map is an actual continuous
map to uniform observations on bounded sets of complex frequencies.

Every exact left inverse on the TRUE data range has a closed graph when
sampling uniquely identifies the source, yet is discontinuous everywhere.
There is no continuous exact reconstruction even if the domain of the
reconstruction is enlarged to ALL uniform sample data, not just the
admissible data range. These claims include nonlinear reconstructions.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- On bounded identifying sampling sets the graph of EVERY exact left
inverse is closed in the product of the true data range and source L²,
even though the exact inverse is nowhere continuous. -/
theorem ultraspherical_fourierBochner_everyExactInverse_closedGraph_nowhereContinuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (r : Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r (ultraspherical_fourierBochner_sampleRangeMap lam S f) = f) :
    IsClosed {p :
        Set.range (ultraspherical_fourierBochner_uniformSamples lam S) ×
          Lp ℂ 2 (Ultraspherical.measure lam) |
      r p.1 = p.2} ∧
    (∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ¬ ContinuousAt r d) := by
  have heq :=
    ultraspherical_fourierBochner_exactSampleInverse_unique lam S r hleft
  rw [heq]
  exact ultraspherical_fourierBochner_canonicalSampleInverse_closedGraph_nowhereContinuous
    lam alpha hlam ha S w R hR hbound hacc

/-- There does not exist a continuous everywhere-defined exact
Fourier–Bochner reconstruction on ALL uniformly observed data,
including arbitrary data that need not be attainable from a source.
This applies to nonlinear reconstructions as well. -/
theorem ultraspherical_fourierBochner_noContinuousAmbientExactReconstruction
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R) :
    ¬ ∃ r : UniformFun S ℂ →
        Lp ℂ 2 (Ultraspherical.measure lam),
      Continuous r ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        r (ultraspherical_fourierBochner_uniformSamples lam S f) = f) := by
  rintro ⟨r, hcont, hleft⟩
  let rrange :
      Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
        Lp ℂ 2 (Ultraspherical.measure lam) :=
    fun d => r d.1
  have hrange_cont : Continuous rrange :=
    hcont.comp continuous_subtype_val
  have hrange_left :
      ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        rrange (ultraspherical_fourierBochner_sampleRangeMap lam S f) = f := by
    intro f
    exact hleft f
  exact (ultraspherical_fourierBochner_uniformSamples_no_continuous_inverse_on_range
    lam alpha hlam ha S R hR hbound)
      ⟨rrange, hrange_cont, hrange_left⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_everyExactInverse_closedGraph_nowhereContinuous
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_noContinuousAmbientExactReconstruction

end GegenbauerFock.GeneralUltrasphericalFock
