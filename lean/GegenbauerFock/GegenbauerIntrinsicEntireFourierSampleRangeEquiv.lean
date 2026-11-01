import GegenbauerFock.GegenbauerIntrinsicEntireFourierSampleRangeBijection

/-!
# V007 — canonical exact Fourier data equivalence without homeomorphism

For a complex frequency set S with a finite accumulation point,
the genuine ultraspherical Fourier–Bochner sampling map is bijective
from its complete L² Hilbert source to its actual range, equipped
with the subspace topology of uniform convergence on S.

This module packages the two certified inverse identities as an
actual Mathlib \`Equiv\`, and proves that when S is bounded, the inverse
of that equivalence is nowhere continuous. The distinction between
algebraic equivalence and a topological isomorphism is explicit.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual Fourier–Bochner map is an equivalence onto its TRUE
set of admissible uniformly sampled data. -/
noncomputable def ultraspherical_fourierBochner_sampleRangeEquiv
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    Lp ℂ 2 (Ultraspherical.measure lam) ≃
      Set.range (ultraspherical_fourierBochner_uniformSamples lam S) where
  toFun := ultraspherical_fourierBochner_sampleRangeMap lam S
  invFun := ultraspherical_fourierBochner_canonicalSampleInverse lam S
  left_inv := ultraspherical_fourierBochner_canonicalSampleInverse_left
    lam alpha hlam ha S w hacc
  right_inv := ultraspherical_fourierBochner_canonicalSampleInverse_right lam S

/-- The reverse direction of the exact Fourier data equivalence is
definitionally the canonical source reconstruction on actual data. -/
theorem ultraspherical_fourierBochner_sampleRangeEquiv_symm_apply
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S)) :
    (ultraspherical_fourierBochner_sampleRangeEquiv
      lam alpha hlam ha S w hacc).symm d =
      ultraspherical_fourierBochner_canonicalSampleInverse lam S d := rfl

/-- On any BOUNDED identifying sample set the inverse of the actual
Fourier data equivalence is discontinuous at EVERY admissible data
vector, despite exact algebraic invertibility. -/
theorem ultraspherical_fourierBochner_sampleRangeEquiv_symm_nowhereContinuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    ∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ¬ ContinuousAt
        (ultraspherical_fourierBochner_sampleRangeEquiv
          lam alpha hlam ha S w hacc).symm d := by
  intro d
  change ¬ ContinuousAt
    (ultraspherical_fourierBochner_canonicalSampleInverse lam S) d
  exact ultraspherical_fourierBochner_canonicalSampleInverse_nowhereContinuous
    lam alpha hlam ha S w R hR hbound hacc d

/-- The exact inverse of the genuine uniform Fourier data equivalence
cannot be globally continuous on any bounded identifying sample set. -/
theorem ultraspherical_fourierBochner_sampleRangeEquiv_symm_not_continuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    ¬ Continuous (ultraspherical_fourierBochner_sampleRangeEquiv
      lam alpha hlam ha S w hacc).symm := by
  intro h
  exact (ultraspherical_fourierBochner_sampleRangeEquiv_symm_nowhereContinuous
    lam alpha hlam ha S w R hR hbound hacc
    (ultraspherical_fourierBochner_sampleRangeMap lam S
      (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) h.continuousAt

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_sampleRangeEquiv_symm_apply
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_sampleRangeEquiv_symm_nowhereContinuous
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_sampleRangeEquiv_symm_not_continuous

end GegenbauerFock.GeneralUltrasphericalFock
