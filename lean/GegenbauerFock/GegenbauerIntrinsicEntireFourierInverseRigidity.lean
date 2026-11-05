import GegenbauerFock.GegenbauerIntrinsicEntireFourierSampleRangeBijection

/-!
# Rigidity of exact reconstruction from ultraspherical Fourier data

The canonical inverse is a function defined on the true Fourier–Bochner
sampling range. It is a RIGHT inverse by construction, without needing
sample accumulation, positivity assumptions, or regularity.

If any (possibly nonlinear) reconstruction on that range is a LEFT
inverse on all L² sources, it MUST equal the canonical inverse.
Consequently, when the sample set is bounded and identifying, every
exact reconstruction is nowhere continuous.

The statements concern the actual Bochner integral sampling operator
and its actual data range, not a formal coefficient surrogate.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Any reconstruction which recovers EVERY ultraspherical L² source
from its true Fourier–Bochner data must equal the canonical inverse.
No injectivity hypothesis is needed: existence of an exact left
inverse itself forces it. -/
theorem ultraspherical_fourierBochner_exactSampleInverse_unique
    (lam : ℝ) (S : Set ℂ)
    (r : Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r (ultraspherical_fourierBochner_sampleRangeMap lam S f) = f) :
    r = ultraspherical_fourierBochner_canonicalSampleInverse lam S := by
  funext d
  calc
    r d =
        r (ultraspherical_fourierBochner_sampleRangeMap lam S
          (ultraspherical_fourierBochner_canonicalSampleInverse lam S d)) :=
      congrArg r
        (ultraspherical_fourierBochner_canonicalSampleInverse_right lam S d).symm
    _ = ultraspherical_fourierBochner_canonicalSampleInverse lam S d :=
      hleft _

/-- On bounded identifying sample sets, every exact source
reconstruction (including nonlinear candidates) is both unique
and nowhere continuous in the inherited uniform-data topology. -/
theorem ultraspherical_fourierBochner_exactSampleInverse_unique_nowhereContinuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (r : Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r (ultraspherical_fourierBochner_sampleRangeMap lam S f) = f) :
    r = ultraspherical_fourierBochner_canonicalSampleInverse lam S ∧
    ∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ¬ ContinuousAt r d := by
  have heq :=
    ultraspherical_fourierBochner_exactSampleInverse_unique lam S r hleft
  refine ⟨heq, ?_⟩
  intro d
  rw [heq]
  exact ultraspherical_fourierBochner_canonicalSampleInverse_nowhereContinuous
    lam alpha hlam ha S w R hR hbound hacc d

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_exactSampleInverse_unique
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_exactSampleInverse_unique_nowhereContinuous

end GegenbauerFock.GeneralUltrasphericalFock
