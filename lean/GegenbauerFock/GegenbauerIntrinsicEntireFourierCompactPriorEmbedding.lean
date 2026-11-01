import GegenbauerFock.GegenbauerIntrinsicEntireFourierContinuousInjectionNonembedding

/-!
# V007 — conditional stability on compact source classes

The genuine ultraspherical Fourier–Bochner sampling operator is
continuous and injective when the complex-frequency set contains
a finite accumulation point. Its inverse on the full infinite-
dimensional L² source space is nowhere continuous when the sampling
frequencies are bounded.

There is a complementary positive result: after restricting the
source to ANY compact subset K of the ultraspherical L² space, the
sampling map IS a topological embedding of K into the uniform-data
space. Thus exact reconstruction restricted to a compact a priori
source class is topologically stable.

This is a topological (not quantitative Lipschitz) stability theorem.
It does not assert that the whole L² unit ball is compact.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For every compact a priori source class, uniform Fourier–Bochner
sampling on a bounded identifying frequency set is a TOPOLOGICAL
EMBEDDING. This contrasts with the non-embedding of full L². -/
theorem ultraspherical_fourierBochner_compactPrior_isEmbedding
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (K : Set (Lp ℂ 2 (Ultraspherical.measure lam)))
    (hK : IsCompact K) :
    Topology.IsEmbedding
      (fun f : K => ultraspherical_fourierBochner_uniformSamples lam S (f : Lp ℂ 2 (Ultraspherical.measure lam))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hF : Continuous (ultraspherical_fourierBochner_uniformSamples lam S) :=
    ultraspherical_fourierBochner_uniformSamples_continuous
      lam alpha hlam ha S R hR hbound
  have hcont :
      Continuous (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam))) :=
    hF.comp continuous_subtype_val
  have hinj :
      Function.Injective (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    intro f g h
    exact Subtype.ext
      ((ultraspherical_fourierBochner_uniformSamples_injective
        lam alpha hlam ha S w hacc) h)
  have hclosed :
      IsClosedMap (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    intro T hT
    exact (hT.isCompact.image hcont).isClosed
  exact (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hcont hinj hclosed).isEmbedding

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_compactPrior_isEmbedding

end GegenbauerFock.GeneralUltrasphericalFock
