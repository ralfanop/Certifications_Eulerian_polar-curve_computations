import GegenbauerFock.GegenbauerIntrinsicEntireFourierContinuousInjectionNonembedding
import Mathlib.Topology.EMetricSpace.Defs

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


/-- On a compact class of sources, the inverse of the genuine
Fourier–Bochner sampling map is uniformly continuous on its actual
sample-data range. This is stronger than mere continuity, but it does
not imply a Lipschitz estimate or an effective numerical modulus. -/
theorem ultraspherical_fourierBochner_compactPrior_inverse_uniformContinuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (K : Set (Lp ℂ 2 (Ultraspherical.measure lam)))
    (hK : IsCompact K) :
    UniformContinuous
      ((ultraspherical_fourierBochner_compactPrior_isEmbedding
        lam alpha hlam ha S w R hR hbound hacc K hK).toHomeomorph.symm) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hEmb := ultraspherical_fourierBochner_compactPrior_isEmbedding
    lam alpha hlam ha S w R hR hbound hacc K hK
  have hRange : IsCompact
      (Set.range (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam)))) :=
    isCompact_range hEmb.continuous
  letI : CompactSpace
      (Set.range (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam)))) :=
    isCompact_iff_compactSpace.mp hRange
  exact CompactSpace.uniformContinuous_of_continuous
    hEmb.toHomeomorph.symm.continuous

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_compactPrior_inverse_uniformContinuous


/-- Every prescribed reconstruction accuracy on a compact a priori class
has a common positive tolerance in extended uniform-data distance.
The tolerance is existential, not an explicit numerical formula. -/
theorem ultraspherical_fourierBochner_compactPrior_inverse_epsilonDelta
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (K : Set (Lp ℂ 2 (Ultraspherical.measure lam)))
    (hK : IsCompact K)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ d e : Set.range (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam))),
        edist d e < δ →
          edist
            ((ultraspherical_fourierBochner_compactPrior_isEmbedding
              lam alpha hlam ha S w R hR hbound hacc K hK).toHomeomorph.symm d)
            ((ultraspherical_fourierBochner_compactPrior_isEmbedding
              lam alpha hlam ha S w R hR hbound hacc K hK).toHomeomorph.symm e) < ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    (EMetric.uniformContinuous_iff.mp
      (ultraspherical_fourierBochner_compactPrior_inverse_uniformContinuous
        lam alpha hlam ha S w R hR hbound hacc K hK)) ε hε
  exact ⟨δ, hδ, fun d e hde => hmod hde⟩

/-- If two compact-class sample data are jointly compatible with a
single possibly noisy observation, their inverse sources are close
whenever the sum of their data discrepancies falls below the
compact-class uniform inverse tolerance. No particular reconstruction
algorithm, Lipschitz modulus, or source outside K is assumed. -/
theorem ultraspherical_fourierBochner_compactPrior_noisyCandidates
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (K : Set (Lp ℂ 2 (Ultraspherical.measure lam)))
    (hK : IsCompact K)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ d e : Set.range (fun f : K =>
        ultraspherical_fourierBochner_uniformSamples lam S
          (f : Lp ℂ 2 (Ultraspherical.measure lam))),
      ∀ y : UniformFun S ℂ,
        edist (d : UniformFun S ℂ) y +
          edist y (e : UniformFun S ℂ) < δ →
          edist
            ((ultraspherical_fourierBochner_compactPrior_isEmbedding
              lam alpha hlam ha S w R hR hbound hacc K hK).toHomeomorph.symm d)
            ((ultraspherical_fourierBochner_compactPrior_isEmbedding
              lam alpha hlam ha S w R hR hbound hacc K hK).toHomeomorph.symm e) < ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    ultraspherical_fourierBochner_compactPrior_inverse_epsilonDelta
      lam alpha hlam ha S w R hR hbound hacc K hK ε hε
  refine ⟨δ, hδ, ?_⟩
  intro d e y hnoisy
  apply hmod d e
  change edist (d : UniformFun S ℂ) (e : UniformFun S ℂ) < δ
  exact lt_of_le_of_lt
    (edist_triangle (d : UniformFun S ℂ) y (e : UniformFun S ℂ))
    hnoisy

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_compactPrior_inverse_epsilonDelta
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_compactPrior_noisyCandidates

end GegenbauerFock.GeneralUltrasphericalFock
