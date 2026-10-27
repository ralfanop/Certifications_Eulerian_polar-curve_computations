import GegenbauerFock.UltrasphericalMomentBounds

/-!
# V007: explicit ultraspherical moments through the true symmetric Beta law

This is an exact change-of-variables identity for the probability
measure defined in UltrasphericalMeasure. It reduces the full
ultraspherical moment problem to the existing normalized Beta measure;
it does NOT evaluate that Beta integral yet.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- General ultraspherical even moments as integrals against the actual
symmetric Beta(shape λ, shape λ) law, not an invented density. -/
theorem evenMoment_eq_beta_integral (lam : ℝ) (n : ℕ) :
    evenMoment lam n =
      ∫ x : ℝ, (betaToInterval x) ^ (2 * n)
        ∂(ProbabilityTheory.betaMeasure (shape lam) (shape lam)) := by
  have hmap : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  unfold evenMoment measure
  rw [integral_map_of_stronglyMeasurable hmap (by fun_prop)]

/-- Positivity of the genuine symmetric Beta probability density. -/
theorem symmetricBetaPDFReal_nonneg (lam : ℝ) (hlam : 0 < lam)
    (x : ℝ) :
    0 ≤ ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x := by
  by_cases hx : 0 < x ∧ x < 1
  · exact (ProbabilityTheory.betaPDFReal_pos hx.1 hx.2
      (shape_pos lam hlam) (shape_pos lam hlam)).le
  · simp [ProbabilityTheory.betaPDFReal, hx]

/-- All even ultraspherical moments are literal weighted Lebesgue
integrals of the normalized symmetric Beta density on ℝ. -/
theorem evenMoment_eq_betaPDFReal_integral
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    evenMoment lam n =
      ∫ x : ℝ,
        ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x *
          (betaToInterval x) ^ (2 * n) ∂volume := by
  rw [evenMoment_eq_beta_integral]
  unfold ProbabilityTheory.betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.ennreal_ofReal
      (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)))
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ProbabilityTheory.betaPDF,
    ENNReal.toReal_ofReal (symmetricBetaPDFReal_nonneg lam hlam x),
    smul_eq_mul]

#print axioms GegenbauerFock.Ultraspherical.symmetricBetaPDFReal_nonneg
#print axioms GegenbauerFock.Ultraspherical.evenMoment_eq_betaPDFReal_integral

#print axioms GegenbauerFock.Ultraspherical.evenMoment_eq_beta_integral

end GegenbauerFock.Ultraspherical
