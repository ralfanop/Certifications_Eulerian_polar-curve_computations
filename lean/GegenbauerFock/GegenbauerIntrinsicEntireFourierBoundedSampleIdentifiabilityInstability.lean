import GegenbauerFock.GegenbauerIntrinsicEntireFourierAccumulationUniqueness
import GegenbauerFock.GegenbauerIntrinsicEntireFourierDiskResolutionLimits

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
open MeasureTheory Set

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

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_boundedSamples_injective
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_boundedSamples_arbitrarilySmall
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_boundedSamples_unique_but_unstable

end GegenbauerFock.GeneralUltrasphericalFock
