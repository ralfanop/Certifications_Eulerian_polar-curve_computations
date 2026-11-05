import GegenbauerFock.UltrasphericalOddReflection

/-!
# V007: all odd ultraspherical moments vanish

The argument uses two actual measures:
* normalized symmetric Beta-pushforward ultraspherical probability measure;
* real Lebesgue measure, invariant under the affine reflection x ↦ 1-x.

No symmetry of an unspecified abstract measure is assumed.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- Actual degree-(2n+1) moment of the ultraspherical law. -/
noncomputable def oddMoment (lam : ℝ) (n : ℕ) : ℝ :=
  ∫ u : ℝ, u ^ (2 * n + 1) ∂(measure lam)

/-- General odd moment as the genuine Beta-density Lebesgue integral. -/
theorem oddMoment_eq_betaPDFReal_integral
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    oddMoment lam n =
      ∫ x : ℝ, oddBetaIntegrand lam n x ∂volume := by
  have hmap : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  unfold oddMoment measure
  rw [integral_map_of_stronglyMeasurable hmap (by fun_prop)]
  unfold ProbabilityTheory.betaMeasure ProbabilityTheory.betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.ennreal_ofReal
      (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)))
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal
    (symmetricBetaPDFReal_nonneg lam hlam x),
    smul_eq_mul, oddBetaIntegrand]

/-- Integral of every symmetric Beta odd integrand is zero. -/
theorem oddBetaIntegrand_integral_eq_zero (lam : ℝ) (n : ℕ) :
    (∫ x : ℝ, oddBetaIntegrand lam n x ∂volume) = 0 := by
  have hmeas : StronglyMeasurable (oddBetaIntegrand lam n) := by
    unfold oddBetaIntegrand betaToInterval
    fun_prop
  have hs :
      (∫ x : ℝ, oddBetaIntegrand lam n (1 - x) ∂volume) =
        ∫ x : ℝ, oddBetaIntegrand lam n x ∂volume := by
    calc
      (∫ x : ℝ, oddBetaIntegrand lam n (1 - x) ∂volume) =
          ∫ x : ℝ, oddBetaIntegrand lam n x
            ∂(Measure.map (fun x : ℝ => 1 - x) volume) :=
              (integral_map_of_stronglyMeasurable (by fun_prop) hmeas).symm
      _ = _ := by rw [volume_map_reflection]
  have hn :
      (∫ x : ℝ, oddBetaIntegrand lam n (1 - x) ∂volume) =
        -(∫ x : ℝ, oddBetaIntegrand lam n x ∂volume) := by
    simp_rw [oddBetaIntegrand_reflection lam n]
    rw [integral_neg]
  linarith

/-- Every odd moment of the general ultraspherical Beta-pushforward law
vanishes; this is an unconditional result for every λ>0. -/
theorem oddMoment_eq_zero
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    oddMoment lam n = 0 := by
  rw [oddMoment_eq_betaPDFReal_integral lam hlam n]
  exact oddBetaIntegrand_integral_eq_zero lam n

#print axioms GegenbauerFock.Ultraspherical.oddMoment_eq_betaPDFReal_integral
#print axioms GegenbauerFock.Ultraspherical.oddBetaIntegrand_integral_eq_zero
#print axioms GegenbauerFock.Ultraspherical.oddMoment_eq_zero

end GegenbauerFock.Ultraspherical
