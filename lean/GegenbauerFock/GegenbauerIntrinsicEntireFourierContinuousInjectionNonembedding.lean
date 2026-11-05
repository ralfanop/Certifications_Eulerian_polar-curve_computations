import GegenbauerFock.GegenbauerIntrinsicEntireFourierUniformForwardContinuity
import GegenbauerFock.GegenbauerIntrinsicEntireFourierSampleRangeEquiv

/-!
# V007 — a continuous injective Fourier map with a nowhere-continuous inverse

For bounded complex sampling sets S with a finite accumulation point,
the genuine ultraspherical Fourier–Bochner sampling map has all of the
following properties simultaneously:

* it is continuous for uniform convergence of observations on S;
* it is injective, so the exact source is uniquely identified;
* it is not a topological embedding of the L² Hilbert norm topology;
* its canonical two-sided inverse on the actual data range is nowhere
  continuous, not merely discontinuous at the zero datum.

This separates exact mathematical identifiability from the stability
of the inverse problem, without replacing the Bochner integral by a
formal coefficient surrogate.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Genuine Fourier–Bochner observations on every bounded frequency
set with a finite accumulation point give a CONTINUOUS INJECTION that
is NOT a topological embedding. -/
theorem ultraspherical_fourierBochner_uniformSamples_continuous_injective_nonembedding
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    Continuous (ultraspherical_fourierBochner_uniformSamples lam S) ∧
    Function.Injective (ultraspherical_fourierBochner_uniformSamples lam S) ∧
    ¬ Topology.IsEmbedding (ultraspherical_fourierBochner_uniformSamples lam S) := by
  exact ⟨ultraspherical_fourierBochner_uniformSamples_continuous
      lam alpha hlam ha S R hR hbound,
    ultraspherical_fourierBochner_uniformSamples_injective
      lam alpha hlam ha S w hacc,
    ultraspherical_fourierBochner_uniformSamples_not_isEmbedding
      lam alpha hlam ha S R hR hbound⟩

/-- The forward Fourier–Bochner sampling map is continuous, but the
inverse direction of its genuine equivalence onto the admissible
uniform-data range is discontinuous at EVERY point of that range. -/
theorem ultraspherical_fourierBochner_sampleRangeEquiv_topological_asymmetry
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    Continuous (ultraspherical_fourierBochner_uniformSamples lam S) ∧
    (∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ¬ ContinuousAt
        (ultraspherical_fourierBochner_sampleRangeEquiv
          lam alpha hlam ha S w hacc).symm d) := by
  exact ⟨ultraspherical_fourierBochner_uniformSamples_continuous
      lam alpha hlam ha S R hR hbound,
    ultraspherical_fourierBochner_sampleRangeEquiv_symm_nowhereContinuous
      lam alpha hlam ha S w R hR hbound hacc⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_continuous_injective_nonembedding
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_sampleRangeEquiv_topological_asymmetry

end GegenbauerFock.GeneralUltrasphericalFock
