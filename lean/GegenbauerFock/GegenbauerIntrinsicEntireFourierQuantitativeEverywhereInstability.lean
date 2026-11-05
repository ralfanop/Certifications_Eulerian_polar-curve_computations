import GegenbauerFock.GegenbauerIntrinsicEntireFourierCanonicalSampleInverse

/-!
# V007 — quantitative Fourier ambiguity around every ultraspherical L² source

The sampled Fourier–Bochner inverse is nowhere continuous. Here we
strengthen the statement in concrete source and observed-data norms.

For EVERY source f, EVERY bounded complex sampling set S and EVERY
positive data tolerance ε, another source g can be found at EXACT L²
distance one, although the genuine Fourier–Bochner integrals of f and
g differ by less than ε at ALL observed frequencies. If S has a
finite accumulation point, f and g are still exactly identifiable:
the obstruction is stability and not uniqueness.

The statements use the actual complex Bochner integrals (not formal
coefficient series or numerical samples).
-/

noncomputable section

open MeasureTheory Set

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Every source has an exact unit-distance perturbation whose genuine
Bochner Fourier observations are uniformly arbitrarily small on S. -/
theorem ultraspherical_fourierBochner_perturbation_unit_distance_small_samples
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖g - f‖ = 1 ∧
      ∀ z ∈ S,
        ‖(∫ v : ℝ, g v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam)) -
          (∫ v : ℝ, f v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam))‖ < ε := by
  obtain ⟨u, hunit, hsmall⟩ :=
    ultraspherical_fourierBochner_boundedSamples_arbitrarilySmall
      lam alpha hlam ha S R hR hbound ε hε
  refine ⟨f + u, ?_, ?_⟩
  · simpa only [add_sub_cancel_left] using hunit
  · intro z hz
    have hadd :
        (∫ v : ℝ, (f + u) v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
        (∫ v : ℝ, f v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) +
        (∫ v : ℝ, u v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) := by
      rw [← evaluatedOperator_eq_integral lam alpha hlam ha z (f + u),
        ← evaluatedOperator_eq_integral lam alpha hlam ha z f,
        ← evaluatedOperator_eq_integral lam alpha hlam ha z u]
      exact map_add (evaluatedOperator lam alpha hlam ha z) f u
    rw [hadd, add_sub_cancel_left]
    exact hsmall z hz

/-- On bounded complex sample sets with a finite accumulation point,
unique identification and arbitrarily close observations at fixed
unit source distance hold simultaneously around EVERY source. -/
theorem ultraspherical_fourierBochner_unique_and_unstable_at_every_source
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (w : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (hacc : w ∈ closure (S \ ({w} : Set ℂ)))
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    (∀ g : Lp ℂ 2 (Ultraspherical.measure lam),
      (∀ z ∈ S,
        (∫ v : ℝ, f v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
        (∫ v : ℝ, g v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam))) → f = g) ∧
    (∀ ε : ℝ, 0 < ε →
      ∃ g : Lp ℂ 2 (Ultraspherical.measure lam),
        ‖g - f‖ = 1 ∧
        ∀ z ∈ S,
          ‖(∫ v : ℝ, g v *
              Complex.exp (Complex.I * z * (v : ℂ) / 2)
              ∂(Ultraspherical.measure lam)) -
            (∫ v : ℝ, f v *
              Complex.exp (Complex.I * z * (v : ℂ) / 2)
              ∂(Ultraspherical.measure lam))‖ < ε) := by
  constructor
  · intro g h
    exact ultraspherical_fourierBochner_boundedSamples_injective
      lam alpha hlam ha S w hacc f g h
  · intro ε hε
    exact ultraspherical_fourierBochner_perturbation_unit_distance_small_samples
      lam alpha hlam ha S R hR hbound f ε hε

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_perturbation_unit_distance_small_samples
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_unique_and_unstable_at_every_source

end GegenbauerFock.GeneralUltrasphericalFock
