import GegenbauerFock.UltrasphericalBetaMoments

/-!
# V007: pushforward integration for arbitrary strongly measurable tests

This is the general (not merely polynomial) test-function identity for
the actual symmetric Beta pushforward measure. It expresses the integral
on the ultraspherical coordinate in terms of the normalized Beta density
on the original coordinate. It does not yet identify the transformed
Lebesgue Radon--Nikodym density on (-1,1), which additionally requires
the affine change-of-variables Jacobian.
-/

open MeasureTheory ProbabilityTheory

namespace GegenbauerFock.Ultraspherical

/-- The concrete ultraspherical pushforward integrates *every* strongly
measurable real test function by the genuine normalized Beta density.
No moment recurrence or hypothetical density is assumed. -/
theorem integral_eq_betaPDFReal_integral
    (lam : ℝ) (hlam : 0 < lam)
    (f : ℝ → ℝ) (hf : StronglyMeasurable f) :
    (∫ u : ℝ, f u ∂(measure lam)) =
      ∫ x : ℝ,
        ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x *
          f (betaToInterval x) ∂volume := by
  have hmap : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  unfold measure
  rw [integral_map_of_stronglyMeasurable hmap hf]
  unfold ProbabilityTheory.betaMeasure ProbabilityTheory.betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.ennreal_ofReal
      (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)))
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (symmetricBetaPDFReal_nonneg lam hlam x),
    smul_eq_mul]

/-- The full Bochner-valued test-function identity for the actual
Beta-pushforward measure. It applies in particular to complex-valued
Fourier kernels, without selecting an L² representative. -/
theorem integral_bochnervalue_eq_betaPDFReal_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (lam : ℝ) (hlam : 0 < lam)
    (f : ℝ → E) (hf : StronglyMeasurable f) :
    (∫ u : ℝ, f u ∂(measure lam)) =
      ∫ x : ℝ,
        ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x •
          f (betaToInterval x) ∂volume := by
  have hmap : Measurable betaToInterval := by
    unfold betaToInterval
    fun_prop
  unfold measure
  rw [integral_map_of_stronglyMeasurable hmap hf]
  unfold ProbabilityTheory.betaMeasure ProbabilityTheory.betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.ennreal_ofReal
      (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)))
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal
    (symmetricBetaPDFReal_nonneg lam hlam x)]

#print axioms GegenbauerFock.Ultraspherical.integral_eq_betaPDFReal_integral
#print axioms GegenbauerFock.Ultraspherical.integral_bochnervalue_eq_betaPDFReal_integral

end GegenbauerFock.Ultraspherical
