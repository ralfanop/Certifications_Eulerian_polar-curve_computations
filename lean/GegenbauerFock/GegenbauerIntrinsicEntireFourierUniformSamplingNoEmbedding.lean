import GegenbauerFock.GegenbauerIntrinsicEntireFourierBoundedSampleIdentifiabilityInstability

/-!
# V007 — uniform complex-frequency sampling is not a topological embedding

For each bounded complex-frequency observation set S, the *genuine* ultraspherical
Fourier–Bochner map into \`UniformFun S ℂ\` fails to be a topological embedding
of the source Hilbert space. This strengthens the corresponding pointwise-data
result and directly distinguishes exact uniqueness from stable reconstruction.

When S also has a finite accumulation point, injectivity of the restricted
map is already certified in the imported module. No finite-sample uniqueness
or numerical reconstruction algorithm is claimed.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The actual Fourier–Bochner transform, restricted to any bounded set of
complex frequencies and endowed with UNIFORM convergence on that set,
does not embed the source Hilbert norm topology. -/
theorem ultraspherical_fourierBochner_uniformSamples_not_isEmbedding
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R) :
    ¬ Topology.IsEmbedding (ultraspherical_fourierBochner_uniformSamples lam S) := by
  intro hemb
  obtain ⟨u, _hunit, huniform, hnostrong⟩ :=
    ultraspherical_fourierBochner_locallyUniform_null_no_strong_source_limit
      lam alpha hlam ha
  have hdata :
      Tendsto (fun n : ℕ =>
        ultraspherical_fourierBochner_uniformSamples lam S (u n))
        atTop (nhds (ultraspherical_fourierBochner_uniformSamples lam S
          (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) := by
    rw [ultraspherical_fourierBochner_uniformSamples_zero lam alpha hlam ha S]
    apply UniformFun.tendsto_iff_tendstoUniformly.mpr
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [huniform R hR ε hε] with n hn z
    have hz := hn (z : ℂ) (hbound (z : ℂ) z.property)
    simpa only [Function.comp_apply, ultraspherical_fourierBochner_uniformSamples,
      UniformFun.toFun_ofFun, UniformFun.toFun_zero, Pi.zero_apply,
      ultraspherical_fourierBochner_function, dist_zero_left, norm_neg] using hz
  have hsource :
      Tendsto u atTop
        (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    exact (hemb.isInducing.tendsto_nhds_iff).2 hdata
  exact hnostrong 0 hsource

/-- Even allowing a nonlinear reconstruction on the TRUE range of uniformly
sampled Fourier–Bochner data, there is no globally continuous left inverse. -/
theorem ultraspherical_fourierBochner_uniformSamples_no_continuous_inverse_on_range
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R) :
    ¬ ∃ r : Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
        Lp ℂ 2 (Ultraspherical.measure lam),
      Continuous r ∧
      (∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
        r ⟨ultraspherical_fourierBochner_uniformSamples lam S f, ⟨f, rfl⟩⟩ = f) := by
  rintro ⟨r, hcont, hleft⟩
  exact (ultraspherical_fourierBochner_uniformSamples_range_inverse_not_continuousAt_zero
    lam alpha hlam ha S R hR hbound r hleft) hcont.continuousAt


/-- For every bounded complex sampling set with a finite accumulation point,
the genuine Fourier–Bochner samples UNIQUELY determine the L² source,
yet the identification is not an embedding of the Hilbert topology
into the uniform topology of the samples. -/
theorem ultraspherical_fourierBochner_uniformSamples_unique_but_not_embedding
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    Function.Injective (ultraspherical_fourierBochner_uniformSamples lam S) ∧
      ¬ Topology.IsEmbedding (ultraspherical_fourierBochner_uniformSamples lam S) := by
  exact ⟨ultraspherical_fourierBochner_uniformSamples_injective
      lam alpha hlam ha S w hacc,
    ultraspherical_fourierBochner_uniformSamples_not_isEmbedding
      lam alpha hlam ha S R hR hbound⟩

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_not_isEmbedding
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_no_continuous_inverse_on_range
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_unique_but_not_embedding

end GegenbauerFock.GeneralUltrasphericalFock
