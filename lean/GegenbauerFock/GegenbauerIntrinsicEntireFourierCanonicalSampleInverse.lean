import GegenbauerFock.GegenbauerIntrinsicEntireFourierUniformInverseNowhereContinuous

/-!
# V007 — actual inverse on bounded, identifying Fourier sample sets

If a complex-frequency sampling set has a finite accumulation point,
the true ultraspherical Fourier–Bochner sampling operator is injective.
Thus it has a unique inverse *on its true range*. We construct this
inverse as an actual function and prove that, for bounded sets, it is
nowhere continuous in the uniform-data topology. This converts the
earlier universal conditional obstruction into a concrete statement
about the existing set-theoretic inverse.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Canonical set-theoretic inverse of the genuine restricted Fourier
transform on its TRUE range, obtained by choosing a source for each
range element. Injectivity will prove independence of this choice. -/
noncomputable def ultraspherical_fourierBochner_canonicalSampleInverse
    (lam : ℝ) (S : Set ℂ) :
    Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
      Lp ℂ 2 (Ultraspherical.measure lam) :=
  fun d => Classical.choose d.property

/-- On every sample set with a finite complex accumulation point,
the canonical inverse exactly reconstructs each source. -/
theorem ultraspherical_fourierBochner_canonicalSampleInverse_left
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ultraspherical_fourierBochner_canonicalSampleInverse lam S
      ⟨ultraspherical_fourierBochner_uniformSamples lam S f, ⟨f, rfl⟩⟩ = f := by
  apply ultraspherical_fourierBochner_uniformSamples_injective
    lam alpha hlam ha S w hacc
  exact Classical.choose_spec
    (show (ultraspherical_fourierBochner_uniformSamples lam S f) ∈
      Set.range (ultraspherical_fourierBochner_uniformSamples lam S)
      from ⟨f, rfl⟩)

/-- The genuine inverse, not merely a hypothetical left inverse, is
nowhere continuous at every admissible data vector of a bounded
identifying frequency set. -/
theorem ultraspherical_fourierBochner_canonicalSampleInverse_nowhereContinuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    ∀ d : Set.range (ultraspherical_fourierBochner_uniformSamples lam S),
      ¬ ContinuousAt (ultraspherical_fourierBochner_canonicalSampleInverse lam S) d := by
  intro d
  obtain ⟨f, hf⟩ := d.property
  have hd :
      (⟨ultraspherical_fourierBochner_uniformSamples lam S f,
        ⟨f, rfl⟩⟩ :
        Set.range (ultraspherical_fourierBochner_uniformSamples lam S)) = d :=
    Subtype.ext hf
  rw [← hd]
  exact ultraspherical_fourierBochner_uniformSamples_inverse_nowhere_continuous
    lam alpha hlam ha S R hR hbound
      (ultraspherical_fourierBochner_canonicalSampleInverse lam S)
      (fun g => ultraspherical_fourierBochner_canonicalSampleInverse_left
        lam alpha hlam ha S w hacc g) f

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_canonicalSampleInverse_left
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_canonicalSampleInverse_nowhereContinuous

end GegenbauerFock.GeneralUltrasphericalFock
