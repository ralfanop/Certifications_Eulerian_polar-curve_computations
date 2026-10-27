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
  unfold evenMoment measure
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  rfl

#print axioms GegenbauerFock.Ultraspherical.evenMoment_eq_beta_integral

end GegenbauerFock.Ultraspherical
