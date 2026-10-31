import GegenbauerFock.GegenbauerIntrinsicEntireFourierCanonicalSampleInverse

/-!
# V007 — genuine Fourier sample range: exact bijection and two-sided inverse

For every sampling set S with a finite complex accumulation point, the
genuine Bochner Fourier map from ultraspherical L² to its *true* uniform
sampling range is bijective. The already certified canonical inverse
is both a left and right inverse on this actual range.

The inverse is nowhere continuous on bounded identifying sets, as
certified separately. Thus algebraic invertibility does not imply a
topological isomorphism.
-/

noncomputable section

open MeasureTheory Set

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual Bochner Fourier transform with codomain restricted to
the exact set of admissible uniformly observed data. -/
noncomputable def ultraspherical_fourierBochner_sampleRangeMap
    (lam : ℝ) (S : Set ℂ) :
    Lp ℂ 2 (Ultraspherical.measure lam) →
      Set.range (ultraspherical_fourierBochner_uniformSamples lam S) :=
  fun f => ⟨ultraspherical_fourierBochner_uniformSamples lam S f, ⟨f, rfl⟩⟩

/-- The canonical set-theoretic inverse reproduces every admissible
Fourier sample datum, even without a sample-accumulation hypothesis. -/
theorem ultraspherical_fourierBochner_canonicalSampleInverse_right
    (lam : ℝ) (S : Set ℂ)
    (d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S)) :
    ultraspherical_fourierBochner_sampleRangeMap lam S
        (ultraspherical_fourierBochner_canonicalSampleInverse lam S d) = d := by
  apply Subtype.ext
  exact Classical.choose_spec d.property

/-- With an accumulation point, the genuine Fourier map is a bijection
of source Hilbert vectors onto the actual uniform-sample data range. -/
theorem ultraspherical_fourierBochner_sampleRangeMap_bijective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    Function.Bijective (ultraspherical_fourierBochner_sampleRangeMap lam S) := by
  constructor
  · intro f g hfg
    have h := congrArg
      (ultraspherical_fourierBochner_canonicalSampleInverse lam S) hfg
    simpa only [ultraspherical_fourierBochner_sampleRangeMap,
      ultraspherical_fourierBochner_canonicalSampleInverse_left
        lam alpha hlam ha S w hacc] using h
  · intro d
    exact ⟨ultraspherical_fourierBochner_canonicalSampleInverse lam S d,
      ultraspherical_fourierBochner_canonicalSampleInverse_right lam S d⟩

/-- Both inverse identities hold simultaneously on genuine Fourier
data, with no extension to the ambient space of arbitrary functions. -/
theorem ultraspherical_fourierBochner_canonicalSampleInverse_twoSided
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ultraspherical_fourierBochner_canonicalSampleInverse lam S
        (ultraspherical_fourierBochner_sampleRangeMap lam S f) = f) ∧
    (∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ultraspherical_fourierBochner_sampleRangeMap lam S
        (ultraspherical_fourierBochner_canonicalSampleInverse lam S d) = d) := by
  constructor
  · exact ultraspherical_fourierBochner_canonicalSampleInverse_left
      lam alpha hlam ha S w hacc
  · exact ultraspherical_fourierBochner_canonicalSampleInverse_right lam S

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_canonicalSampleInverse_right
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_sampleRangeMap_bijective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_canonicalSampleInverse_twoSided

end GegenbauerFock.GeneralUltrasphericalFock
