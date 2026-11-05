import GegenbauerFock.GegenbauerIntrinsicEntireFourierUniformSamplingNoEmbedding

/-!
# V007 — the inverse of uniform Fourier–Bochner sampling is nowhere continuous

On every bounded complex-frequency set S the actual Fourier–Bochner
sampling operator has arbitrarily small uniform data along a unit-norm
source sequence. By complex linearity of the actual Bochner evaluation,
this obstruction persists after translation by *any* source f.

Consequently every exact left inverse defined on the actual sampled
range is discontinuous at EVERY data vector in that range, even if the
inverse is nonlinear. No finite-sample uniqueness is assumed.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- The original uniform-frequency Bochner sampling map is additive. -/
theorem ultraspherical_fourierBochner_uniformSamples_add
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ)
    (f g : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ultraspherical_fourierBochner_uniformSamples lam S (f + g) =
      ultraspherical_fourierBochner_uniformSamples lam S f +
        ultraspherical_fourierBochner_uniformSamples lam S g := by
  apply UniformFun.toFun.injective
  funext z
  change (∫ v : ℝ, (f + g) v *
      Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
      ∂(Ultraspherical.measure lam)) =
    (∫ v : ℝ, f v *
      Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
      ∂(Ultraspherical.measure lam)) +
    (∫ v : ℝ, g v *
      Complex.exp (Complex.I * (z : ℂ) * (v : ℂ) / 2)
      ∂(Ultraspherical.measure lam))
  rw [← evaluatedOperator_eq_integral lam alpha hlam ha (z : ℂ) (f + g),
      ← evaluatedOperator_eq_integral lam alpha hlam ha (z : ℂ) f,
      ← evaluatedOperator_eq_integral lam alpha hlam ha (z : ℂ) g]
  exact map_add (evaluatedOperator lam alpha hlam ha (z : ℂ)) f g

/-- Every exact left inverse on the TRUE range of sampled Fourier–Bochner
data fails to be continuous at the datum of an ARBITRARY source f.
The range carries the subspace topology inherited from uniform convergence. -/
theorem ultraspherical_fourierBochner_uniformSamples_inverse_nowhere_continuous
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (r : Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
       Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r ⟨ultraspherical_fourierBochner_uniformSamples lam S f, ⟨f, rfl⟩⟩ = f)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    ¬ ContinuousAt r
      (⟨ultraspherical_fourierBochner_uniformSamples lam S f, ⟨f, rfl⟩⟩ :
        Set.range (ultraspherical_fourierBochner_uniformSamples lam S)) := by
  intro hcont
  obtain ⟨u, _hunit, huniform, hnostrong⟩ :=
    ultraspherical_fourierBochner_locallyUniform_null_no_strong_source_limit
      lam alpha hlam ha
  have hdata :
      Tendsto (fun n : ℕ =>
        ultraspherical_fourierBochner_uniformSamples lam S (u n))
        atTop (nhds (0 : UniformFun S ℂ)) := by
    apply UniformFun.tendsto_iff_tendstoUniformly.mpr
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [huniform R hR ε hε] with n hn z
    have hz := hn (z : ℂ) (hbound (z : ℂ) z.property)
    simpa only [Function.comp_apply, ultraspherical_fourierBochner_uniformSamples,
      UniformFun.toFun_ofFun, UniformFun.toFun_zero, Pi.zero_apply,
      ultraspherical_fourierBochner_function, dist_zero_left, norm_neg] using hz
  have htranslated :
      Tendsto (fun n : ℕ =>
        ultraspherical_fourierBochner_uniformSamples lam S (f + u n))
        atTop
        (nhds (ultraspherical_fourierBochner_uniformSamples lam S f)) := by
    have h := (tendsto_const_nhds (x :=
      ultraspherical_fourierBochner_uniformSamples lam S f)).add hdata
    simpa only [add_zero, ← ultraspherical_fourierBochner_uniformSamples_add
      lam alpha hlam ha S] using h
  have hsub :
      Tendsto (fun n : ℕ =>
        (⟨ultraspherical_fourierBochner_uniformSamples lam S (f + u n),
          ⟨f + u n, rfl⟩⟩ :
          Set.range (ultraspherical_fourierBochner_uniformSamples lam S)))
        atTop
        (nhds (⟨ultraspherical_fourierBochner_uniformSamples lam S f,
          ⟨f, rfl⟩⟩ :
          Set.range (ultraspherical_fourierBochner_uniformSamples lam S))) := by
    exact tendsto_subtype_rng.mpr htranslated
  have hrec := hcont.tendsto.comp hsub
  change Tendsto
      (fun n : ℕ =>
        r ⟨ultraspherical_fourierBochner_uniformSamples lam S (f + u n),
          ⟨f + u n, rfl⟩⟩)
      atTop
      (nhds (r ⟨ultraspherical_fourierBochner_uniformSamples lam S f,
        ⟨f, rfl⟩⟩)) at hrec
  have hsource :
      (fun n : ℕ =>
        r ⟨ultraspherical_fourierBochner_uniformSamples lam S (f + u n),
          ⟨f + u n, rfl⟩⟩) = (fun n : ℕ => f + u n) := by
    funext n
    exact hleft (f + u n)
  rw [hsource, hleft f] at hrec
  have hnull : Tendsto u atTop
      (nhds (0 : Lp ℂ 2 (Ultraspherical.measure lam))) := by
    have h := hrec.sub (tendsto_const_nhds (x := f))
    simpa only [add_sub_cancel_left, sub_self] using h
  exact hnostrong 0 hnull

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_add
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_inverse_nowhere_continuous

end GegenbauerFock.GeneralUltrasphericalFock
