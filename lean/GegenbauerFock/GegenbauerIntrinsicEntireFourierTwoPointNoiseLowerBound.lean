import GegenbauerFock.GegenbauerIntrinsicEntireFourierQuantitativeEverywhereInstability

/-!
# V007 — quantitative two-point lower bound against robust reconstruction

For any bounded complex-frequency sampling window, any ultraspherical
source f, any positive data tolerance ε, and ANY deterministic
reconstructor r (linear or nonlinear, continuous or discontinuous),
there exists a different source g at unit L² distance whose actual
Bochner observations differ from those of f by < ε at EVERY observed
frequency.

A single observed datum y = F(f) is therefore consistent with the
source f without noise and with g under uniformly ε-small pointwise
noise. The same deterministic reconstruction r(y) has error ≥ 1/2
at one of the two possible sources, by the metric triangle inequality.

The second theorem rules out a globally <1/2-accurate recovery rule
for all sources when their measured Fourier data may be ε-perturbed.
These are genuine integral observations, not a formal coefficient map.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- At every source, under arbitrarily small pointwise sampling noise,
any reconstruction rule has error at least 1/2 on one of two
unit-separated admissible sources. -/
theorem ultraspherical_fourierBochner_twoPoint_noise_lowerBound
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (r : UniformFun S ℂ → Lp ℂ 2 (Ultraspherical.measure lam))
    (f : Lp ℂ 2 (Ultraspherical.measure lam))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖g - f‖ = 1 ∧
      (∀ z ∈ S,
        ‖(∫ v : ℝ, g v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam)) -
          (∫ v : ℝ, f v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam))‖ < ε) ∧
      ((1 / 2 : ℝ) ≤
          dist (r (ultraspherical_fourierBochner_uniformSamples lam S f)) f ∨
        (1 / 2 : ℝ) ≤
          dist (r (ultraspherical_fourierBochner_uniformSamples lam S f)) g) := by
  obtain ⟨g, hunit, hsmall⟩ :=
    ultraspherical_fourierBochner_perturbation_unit_distance_small_samples
      lam alpha hlam ha S R hR hbound f ε hε
  refine ⟨g, hunit, hsmall, ?_⟩
  let y := ultraspherical_fourierBochner_uniformSamples lam S f
  by_cases hf : (1 / 2 : ℝ) ≤ dist (r y) f
  · exact Or.inl hf
  · right
    by_contra hg
    have hf' : dist (r y) f < (1 / 2 : ℝ) := lt_of_not_ge hf
    have hg' : dist (r y) g < (1 / 2 : ℝ) := lt_of_not_ge hg
    have hsep : dist g f = 1 := by
      simpa only [dist_eq_norm] using hunit
    have htri := dist_triangle g (r y) f
    rw [dist_comm g (r y)] at htri
    linarith

/-- No deterministic reconstruction from uniformly sampled genuine
Fourier–Bochner data achieves strict L² error less than 1/2 for EVERY
source subject to any positive uniform pointwise error tolerance. -/
theorem ultraspherical_fourierBochner_noUniformRobustRecovery_belowHalf
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (r : UniformFun S ℂ → Lp ℂ 2 (Ultraspherical.measure lam))
    (ε : ℝ) (hε : 0 < ε) :
    ¬ ∀ f g : Lp ℂ 2 (Ultraspherical.measure lam),
        (∀ z ∈ S,
          ‖(∫ v : ℝ, g v *
              Complex.exp (Complex.I * z * (v : ℂ) / 2)
              ∂(Ultraspherical.measure lam)) -
            (∫ v : ℝ, f v *
              Complex.exp (Complex.I * z * (v : ℂ) / 2)
              ∂(Ultraspherical.measure lam))‖ < ε) →
        dist (r (ultraspherical_fourierBochner_uniformSamples lam S f)) g <
          (1 / 2 : ℝ) := by
  intro hrobust
  obtain ⟨g, _hunit, hsmall, hbad⟩ :=
    ultraspherical_fourierBochner_twoPoint_noise_lowerBound
      lam alpha hlam ha S R hR hbound r
      (0 : Lp ℂ 2 (Ultraspherical.measure lam)) ε hε
  have hself :
      dist (r (ultraspherical_fourierBochner_uniformSamples lam S
          (0 : Lp ℂ 2 (Ultraspherical.measure lam))))
          (0 : Lp ℂ 2 (Ultraspherical.measure lam)) < (1 / 2 : ℝ) := by
    apply hrobust 0 0
    intro z hz
    simpa only [sub_self, norm_zero] using hε
  have hpert :
      dist (r (ultraspherical_fourierBochner_uniformSamples lam S
          (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) g < (1 / 2 : ℝ) :=
    hrobust 0 g hsmall
  rcases hbad with hbad | hbad
  · exact (not_lt_of_ge hbad) hself
  · exact (not_lt_of_ge hbad) hpert

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_twoPoint_noise_lowerBound
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_noUniformRobustRecovery_belowHalf

end GegenbauerFock.GeneralUltrasphericalFock
