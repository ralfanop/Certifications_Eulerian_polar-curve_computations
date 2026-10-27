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
  unfold ProbabilityTheory.betaMeasure ProbabilityTheory.betaPDF
  rw [integral_withDensity_eq_integral_toReal_smul
    (Measurable.ennreal_ofReal
      (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)))
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ProbabilityTheory.betaPDF,
    ENNReal.toReal_ofReal (symmetricBetaPDFReal_nonneg lam hlam x),
    smul_eq_mul]

/-- Integrability, with respect to real Lebesgue measure, of the actual
Beta density multiplied by any even ultraspherical monomial. This is
derived from the normalized Beta probability law, without an assumed
moment formula. -/
theorem evenMoment_betaPDF_integrable
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ) :
    Integrable (fun x : ℝ =>
      ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x *
        (betaToInterval x) ^ (2 * n)) volume := by
  letI : IsProbabilityMeasure
      (ProbabilityTheory.betaMeasure (shape lam) (shape lam)) :=
    ProbabilityTheory.isProbabilityMeasureBeta
      (shape_pos lam hlam) (shape_pos lam hlam)
  have hp : Integrable (fun x : ℝ => (betaToInterval x) ^ (2 * n))
      (ProbabilityTheory.betaMeasure (shape lam) (shape lam)) := by
    apply Integrable.of_bound (by
      have hmeas : Measurable (fun x : ℝ => (betaToInterval x) ^ (2 * n)) := by
        unfold betaToInterval
        fun_prop
      exact hmeas.aestronglyMeasurable) 1
    filter_upwards [beta_ae_unit_interval lam] with x hx
    have habs : |betaToInterval x| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> unfold betaToInterval <;> linarith [hx.1, hx.2]
    calc
      ‖(betaToInterval x) ^ (2 * n)‖ = |betaToInterval x| ^ (2 * n) := by
        simp [norm_pow]
      _ ≤ (1 : ℝ) ^ (2 * n) := by gcongr
      _ = 1 := by simp
  change Integrable (fun x : ℝ => (betaToInterval x) ^ (2 * n))
    (volume.withDensity (ProbabilityTheory.betaPDF (shape lam) (shape lam))) at hp
  have h :=
    (integrable_withDensity_iff_integrable_smul'
      (Measurable.ennreal_ofReal
        (ProbabilityTheory.measurable_betaPDFReal (shape lam) (shape lam)))
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hp
  convert h using 1
  ext x
  simp only [ProbabilityTheory.betaPDF,
    ENNReal.toReal_ofReal (symmetricBetaPDFReal_nonneg lam hlam x),
    smul_eq_mul]

/-- An elementary integration-by-parts primitive for ultraspherical
moments, defined on the original symmetric Beta coordinate. -/
private noncomputable def momentRecurrencePrimitive
    (lam : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  betaToInterval x ^ (2 * n + 1) *
    x ^ (shape lam) * (1 - x) ^ (shape lam)

/-- The weighted derivative predicted by integration by parts. -/
private noncomputable def momentRecurrenceIntegrand
    (lam : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ProbabilityTheory.beta (shape lam) (shape lam) *
    (((n : ℝ) + 1 / 2) *
        (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x *
          betaToInterval x ^ (2 * n)) -
      ((n : ℝ) + lam + 1) *
        (ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x *
          betaToInterval x ^ (2 * (n + 1))))

/-- The primitive has the exact weighted moment-recursion derivative
at each point of the open beta support (0,1). -/
private theorem momentRecurrencePrimitive_hasDerivAt
    (lam : ℝ) (hlam : 0 < lam) (n : ℕ)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    HasDerivAt (momentRecurrencePrimitive lam n)
      (momentRecurrenceIntegrand lam n x) x := by
  have ha : 0 < shape lam := shape_pos lam hlam
  have hy : 0 < 1 - x := by linarith
  have hd_u : HasDerivAt betaToInterval 2 x := by
    convert (((hasDerivAt_id x).const_mul (2 : ℝ)).sub_const 1) using 1 <;> ring
  have hd_pow :
      HasDerivAt (fun t : ℝ => betaToInterval t ^ (2 * n + 1))
        (((2 * n + 1 : ℕ) : ℝ) * betaToInterval x ^ (2 * n) * 2) x := by
    simpa only [Nat.add_sub_cancel] using (hd_u.pow (2 * n + 1))
  have hd_x : HasDerivAt (fun t : ℝ => t ^ (shape lam))
      (shape lam * x ^ (shape lam - 1)) x := by
    convert (hasDerivAt_id x).rpow_const (Or.inl hx0.ne') using 1 <;> ring
  have hd_y : HasDerivAt (fun t : ℝ => (1 - t) ^ (shape lam))
      (-(shape lam) * (1 - x) ^ (shape lam - 1)) x := by
    have hm : HasDerivAt (fun t : ℝ => (1 : ℝ) - t) (-1) x := by
      convert (hasDerivAt_id x).const_sub 1 using 1 <;> ring
    convert hm.rpow_const (Or.inl hy.ne') using 1 <;> ring
  have hraw : HasDerivAt (momentRecurrencePrimitive lam n)
      ((((2 * n + 1 : ℕ) : ℝ) * betaToInterval x ^ (2 * n) * 2) *
          x ^ (shape lam) * (1 - x) ^ (shape lam) +
        (betaToInterval x ^ (2 * n + 1) *
          (shape lam * x ^ (shape lam - 1))) * (1 - x) ^ (shape lam) +
        (betaToInterval x ^ (2 * n + 1) * x ^ (shape lam)) *
          (-(shape lam) * (1 - x) ^ (shape lam - 1))) x := by
    convert ((hd_pow.mul hd_x).mul hd_y) using 1 <;>
      simp only [momentRecurrencePrimitive] <;> ring
  have hxa : x ^ (shape lam) = x ^ (shape lam - 1) * x := by
    rw [show shape lam = (shape lam - 1) + 1 by ring,
      Real.rpow_add hx0 (shape lam - 1) 1, Real.rpow_one]
  have hya : (1 - x) ^ (shape lam) =
      (1 - x) ^ (shape lam - 1) * (1 - x) := by
    rw [show shape lam = (shape lam - 1) + 1 by ring,
      Real.rpow_add hy (shape lam - 1) 1, Real.rpow_one]
  have hodd : betaToInterval x ^ (2 * n + 1) =
      betaToInterval x ^ (2 * n) * betaToInterval x := by
    rw [show 2 * n + 1 = 2 * n + 1 by rfl, pow_succ]
  have heven : betaToInterval x ^ (2 * (n + 1)) =
      betaToInterval x ^ (2 * n) * betaToInterval x ^ 2 := by
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
  have hpdf : ProbabilityTheory.beta (shape lam) (shape lam) *
      ProbabilityTheory.betaPDFReal (shape lam) (shape lam) x =
      x ^ (shape lam - 1) * (1 - x) ^ (shape lam - 1) := by
    rw [ProbabilityTheory.betaPDFReal, if_pos ⟨hx0, hx1⟩]
    field_simp [(ProbabilityTheory.beta_pos ha ha).ne']
  have hfactor : momentRecurrenceIntegrand lam n x =
      x ^ (shape lam - 1) * (1 - x) ^ (shape lam - 1) *
        (((n : ℝ) + 1 / 2) * betaToInterval x ^ (2 * n) -
          ((n : ℝ) + lam + 1) * betaToInterval x ^ (2 * (n + 1))) := by
    unfold momentRecurrenceIntegrand
    rw [← hpdf]
    ring
  convert hraw using 1
  rw [hfactor, hxa, hya, hodd, heven]
  unfold betaToInterval shape
  ring

#print axioms GegenbauerFock.Ultraspherical.evenMoment_betaPDF_integrable
#print axioms GegenbauerFock.Ultraspherical.symmetricBetaPDFReal_nonneg
#print axioms GegenbauerFock.Ultraspherical.evenMoment_eq_betaPDFReal_integral

#print axioms GegenbauerFock.Ultraspherical.evenMoment_eq_beta_integral

end GegenbauerFock.Ultraspherical
