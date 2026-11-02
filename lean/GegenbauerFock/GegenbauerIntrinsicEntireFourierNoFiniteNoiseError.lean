import GegenbauerFock.GegenbauerIntrinsicEntireFourierTwoPointNoiseLowerBound

/-!
# V007 — no finite global noisy Fourier reconstruction error bound

The previously certified approximate-null directions are normalized to
L² norm one. Linearity of the genuine Fourier–Bochner evaluation allows
rescaling those directions to any prescribed positive L² norm while
keeping every observation in a bounded frequency window arbitrarily
small. Thus the two-source noisy-reconstruction lower bound extends
from 1/2 to arbitrarily large error: no finite global worst-case
reconstruction bound exists without a bounded/compact source prior.

The data estimates below concern actual complex Bochner integrals.
-/

noncomputable section

open MeasureTheory Set

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- For any prescribed source magnitude N > 0, there is a source of
EXACT norm N whose genuine Fourier–Bochner data on S are pointwise
uniformly bounded by an arbitrarily small tolerance ε > 0. -/
theorem ultraspherical_fourierBochner_arbitrarilyLarge_approximateNull
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (N ε : ℝ) (hN : 0 < N) (hε : 0 < ε) :
    ∃ g : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖g‖ = N ∧
      ∀ z ∈ S,
        ‖∫ v : ℝ, g v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ < ε := by
  obtain ⟨u, hu, hsmall⟩ :=
    ultraspherical_fourierBochner_boundedSamples_arbitrarilySmall
      lam alpha hlam ha S R hR hbound (ε / N) (div_pos hε hN)
  have hcnorm : ‖(N : ℂ)‖ = N :=
    Complex.norm_of_nonneg (le_of_lt hN)
  refine ⟨(N : ℂ) • u, ?_, ?_⟩
  · rw [norm_smul, hcnorm, hu, mul_one]
  · intro z hz
    have hscaled :
        (∫ v : ℝ, ((N : ℂ) • u) v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) =
          (N : ℂ) *
            (∫ v : ℝ, u v *
              Complex.exp (Complex.I * z * (v : ℂ) / 2)
              ∂(Ultraspherical.measure lam)) := by
      rw [← evaluatedOperator_eq_integral lam alpha hlam ha z ((N : ℂ) • u),
        ← evaluatedOperator_eq_integral lam alpha hlam ha z u]
      simpa only [smul_eq_mul] using
        (map_smul (evaluatedOperator lam alpha hlam ha z) (N : ℂ) u)
    calc
      ‖∫ v : ℝ, ((N : ℂ) • u) v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)‖ =
          N * ‖∫ v : ℝ, u v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam)‖ := by
              rw [hscaled, norm_mul, hcnorm]
      _ < N * (ε / N) :=
        mul_lt_mul_of_pos_left (hsmall z hz) hN
      _ = ε := by
        field_simp [ne_of_gt hN]

/-- Every deterministic reconstruction rule has arbitrarily large
worst-case L² error under arbitrarily small genuine Fourier data noise,
already at the observed datum of the zero source. No bounded source
prior is imposed. -/
theorem ultraspherical_fourierBochner_noFiniteGlobalNoiseError
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (S : Set ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z ∈ S, ‖z‖ ≤ R)
    (r : UniformFun S ℂ → Lp ℂ 2 (Ultraspherical.measure lam))
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ g : Lp ℂ 2 (Ultraspherical.measure lam),
      ‖g‖ = 2 * B + 1 ∧
      (∀ z ∈ S,
        ‖(∫ v : ℝ, g v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam)) -
          (∫ v : ℝ, (0 : Lp ℂ 2 (Ultraspherical.measure lam)) v *
            Complex.exp (Complex.I * z * (v : ℂ) / 2)
            ∂(Ultraspherical.measure lam))‖ < ε) ∧
      (B < dist
          (r (ultraspherical_fourierBochner_uniformSamples lam S
            (0 : Lp ℂ 2 (Ultraspherical.measure lam))))
          (0 : Lp ℂ 2 (Ultraspherical.measure lam)) ∨
       B < dist
          (r (ultraspherical_fourierBochner_uniformSamples lam S
            (0 : Lp ℂ 2 (Ultraspherical.measure lam)))) g) := by
  have hmag : 0 < 2 * B + 1 := by linarith
  obtain ⟨g, hg, hsmall⟩ :=
    ultraspherical_fourierBochner_arbitrarilyLarge_approximateNull
      lam alpha hlam ha S R hR hbound (2 * B + 1) ε hmag hε
  refine ⟨g, hg, ?_, ?_⟩
  · intro z hz
    have hzero :
        (∫ v : ℝ, (0 : Lp ℂ 2 (Ultraspherical.measure lam)) v *
          Complex.exp (Complex.I * z * (v : ℂ) / 2)
          ∂(Ultraspherical.measure lam)) = 0 := by
      rw [← evaluatedOperator_eq_integral lam alpha hlam ha z
        (0 : Lp ℂ 2 (Ultraspherical.measure lam))]
      exact map_zero (evaluatedOperator lam alpha hlam ha z)
    simpa only [hzero, sub_zero] using hsmall z hz
  · let y := ultraspherical_fourierBochner_uniformSamples lam S
      (0 : Lp ℂ 2 (Ultraspherical.measure lam))
    by_cases hzero : B < dist (r y) (0 : Lp ℂ 2 (Ultraspherical.measure lam))
    · exact Or.inl hzero
    · right
      have hz : dist (r y) (0 : Lp ℂ 2 (Ultraspherical.measure lam)) ≤ B :=
        le_of_not_gt hzero
      have htri := dist_triangle g (r y) (0 : Lp ℂ 2 (Ultraspherical.measure lam))
      rw [dist_comm g (r y)] at htri
      have hdist : dist g (0 : Lp ℂ 2 (Ultraspherical.measure lam)) =
          2 * B + 1 := by
        simpa only [dist_eq_norm, sub_zero] using hg
      rw [hdist] at htri
      linarith

#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_arbitrarilyLarge_approximateNull
#print axioms GegenbauerFock.GeneralUltrasphericalFock.ultraspherical_fourierBochner_noFiniteGlobalNoiseError

end GegenbauerFock.GeneralUltrasphericalFock
