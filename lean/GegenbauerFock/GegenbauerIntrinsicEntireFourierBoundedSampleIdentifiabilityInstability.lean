import GegenbauerFock.GegenbauerIntrinsicEntireFourierAccumulationUniqueness
import GegenbauerFock.GegenbauerIntrinsicEntireFourierDiskResolutionLimits
import GegenbauerFock.GegenbauerIntrinsicEntireFourierNotTopologicalEmbedding
import Mathlib.Topology.Algebra.UniformConvergence

/-!
# V007 — exact uniqueness without stable inversion on bounded sampling sets

Even when an arbitrary bounded frequency set S ⊆ ℂ contains an
accumulation point, so that genuine Fourier–Bochner values on S
uniquely determine the entire ultraspherical L² source, these same
observations fail to control the L² norm uniformly.

The two properties are distinct:
* exact injectivity is proved by the certified analytic identity
  theorem plus full intrinsic Gaussian-Fock source injectivity;
* arbitrarily small observations of a UNIT L² input follow from the
  separately certified uniform complex-disk approximate-null theorem.

In particular, the result applies to bounded *countably infinite*
sample sets with an accumulation point. No claim of finite-sample
uniqueness or norm-stable reconstruction is made.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Exact Fourier–Bochner values on any frequency set S with a finite
accumulation point uniquely determine every ultraspherical L² source.
This theorem records the restriction explicitly to a bounded window. -/
theorem ultraspherical_fourierBochner_boundedSamples_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (f g : Lp ℂ 2 (Ultraspherical.measure lam))
    (h : ∀ z ∈ S,
      (∫ u : ℝ, f u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam)) =
      (∫ u : ℝ, g u *
        Complex.exp (Complex.I * z * (u : ℂ) / 2)
        ∂(Ultraspherical.measure lam))) :
    f = g := by
  exact ultraspherical_fourierBochner_injective_of_accumulation_samples
    lam alpha hlam ha S w hacc f g h

/-- Any bounded complex-frequency sampling set can have arbitrary
small actual Bochner Fourier data from a SOURCE OF NORM ONE. -/
theorem ultraspherical_fourierBochner_boundedSamples_arbitrarilySmall
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖f‖ = 1 ∧
      ∀ z ∈ S,
        ‖∫ u : ℝ, f u *
          Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ < ε := by
  obtain ⟨f, hf, hsmall⟩ :=
    ultraspherical_fourierBochner_arbitrarilySmall_on_disk
      lam alpha hlam ha R hR ε hε
  refine ⟨f, hf, ?_⟩
  intro z hz
  exact hsmall z (hbound z hz)

/-- Unique source identification and arbitrarily poor stability coexist
on ANY bounded frequency set with a finite accumulation point. -/
theorem ultraspherical_fourierBochner_boundedSamples_unique_but_unstable
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ)
    (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    (∀ f g : Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ z ∈ S,
        (∫ u : ℝ, f u *
          Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
        (∫ u : ℝ, g u *
          Complex.exp (Complex.I * z * (u : ℂ) / 2)
          ∂(Ultraspherical.measure lam))) → f = g) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ f : Lp ℂ 2 (Ultraspherical.measure lam),
        ‖f‖ = 1 ∧
        ∀ z ∈ S,
          ‖∫ u : ℝ, f u *
            Complex.exp (Complex.I * z * (u : ℂ) / 2)
            ∂(Ultraspherical.measure lam)‖ < ε) := by
  constructor
  · intro f g h
    exact ultraspherical_fourierBochner_boundedSamples_injective
      lam alpha hlam ha S w hacc f g h
  · intro ε hε
    exact ultraspherical_fourierBochner_boundedSamples_arbitrarilySmall
      lam alpha hlam ha S R hR hbound ε hε


/-!
## Uniform topology of bounded samples: discontinuity on the true data range

The codomain is the genuine Mathlib uniform-convergence function space
\`UniformFun S ℂ\`, not merely the pointwise product topology.  This
strengthens the earlier inverse obstruction to the uniform sampling
topology, even when reconstruction is defined only on the exact image.
-/

/-- Restriction of the actual Fourier–Bochner integral to S, regarded
as a function with the topology of UNIFORM convergence over S. -/
noncomputable def ultraspherical_fourierBochner_uniformSamples
    (lam : ℝ) (S : Set ℂ)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) : UniformFun S ℂ :=
  UniformFun.ofFun (fun z : S =>
    ultraspherical_fourierBochner_function lam f z)

/-- Zero input has zero restricted Fourier data in the uniform topology. -/
theorem ultraspherical_fourierBochner_uniformSamples_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) :
    ultraspherical_fourierBochner_uniformSamples lam S
      (0 : Lp ℂ 2 (Ultraspherical.measure lam)) =
        (0 : UniformFun S ℂ) := by
  apply UniformFun.toFun.injective
  funext z
  have hz := congrFun (ultraspherical_fourierBochner_function_zero
    lam alpha hlam ha) (z : ℂ)
  simpa only [ultraspherical_fourierBochner_uniformSamples,
    UniformFun.toFun_ofFun, UniformFun.toFun_zero, Pi.zero_apply] using hz

/-- Uniqueness of ultraspherical inputs from S, expressed directly
as injectivity of the restricted Fourier map into the uniform space. -/
theorem ultraspherical_fourierBochner_uniformSamples_injective
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ))) :
    Function.Injective (ultraspherical_fourierBochner_uniformSamples lam S) := by
  intro f g hfg
  apply ultraspherical_fourierBochner_boundedSamples_injective
    lam alpha hlam ha S w hacc f g
  intro z hz
  have hval := congrArg
    (fun h : UniformFun S ℂ => UniformFun.toFun h ⟨z, hz⟩) hfg
  simpa only [ultraspherical_fourierBochner_uniformSamples,
    UniformFun.toFun_ofFun, ultraspherical_fourierBochner_function] using hval

/-- On every bounded frequency set S, no left inverse on the TRUE
range of the restricted Fourier–Bochner map is continuous at zero
in the topology of UNIFORM convergence on S. The inverse may be
nonlinear and is not required to extend to all functions on S. -/
theorem ultraspherical_fourierBochner_uniformSamples_range_inverse_not_continuousAt_zero
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (r : Set.range (ultraspherical_fourierBochner_uniformSamples lam S) →
      Lp ℂ 2 (Ultraspherical.measure lam))
    (hleft : ∀ f : Lp ℂ 2 (Ultraspherical.measure lam),
      r ⟨ultraspherical_fourierBochner_uniformSamples lam S f, ⟨f, rfl⟩⟩ = f) :
    ¬ ContinuousAt r
      (⟨ultraspherical_fourierBochner_uniformSamples lam S
        (0 : Lp ℂ 2 (Ultraspherical.measure lam)), ⟨0, rfl⟩⟩ :
        Set.range (ultraspherical_fourierBochner_uniformSamples lam S)) := by
  intro hcont
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
  have hsub :
      Tendsto (fun n : ℕ =>
        (⟨ultraspherical_fourierBochner_uniformSamples lam S (u n),
          ⟨u n, rfl⟩⟩ :
          Set.range (ultraspherical_fourierBochner_uniformSamples lam S)))
        atTop
        (nhds (⟨ultraspherical_fourierBochner_uniformSamples lam S
            (0 : Lp ℂ 2 (Ultraspherical.measure lam)), ⟨0, rfl⟩⟩ :
            Set.range (ultraspherical_fourierBochner_uniformSamples lam S))) := by
    exact tendsto_subtype_rng.mpr hdata
  have hrec := hcont.tendsto.comp hsub
  have hsrc :
      (fun n : ℕ =>
        r ⟨ultraspherical_fourierBochner_uniformSamples lam S (u n),
          ⟨u n, rfl⟩⟩) = u := by
    funext n
    exact hleft (u n)
  have hrec' := hrec
  simp only [Function.comp_def, hsrc] at hrec'
  exact hnostrong _ hrec'


#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_boundedSamples_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_boundedSamples_arbitrarilySmall
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_boundedSamples_unique_but_unstable

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_zero
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_uniformSamples_range_inverse_not_continuousAt_zero

end GegenbauerFock.GeneralUltrasphericalFock
