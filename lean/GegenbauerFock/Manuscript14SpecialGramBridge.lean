import GegenbauerFock.GramNuclearTrace

/-!
# Manuscript 14.1, Section 6 — actual complex L² Eulerian Gram operator

This V007-derived compatibility module specializes *existing kernel proofs*
to λ = 1/2 and α = 1/√2. The resulting exponential parameter
1/(4α) equals the manuscript's a = 1/√8.

It connects the actual bounded L² Gram to an operator-valued Bochner
integral, a summable rank-one nuclear decomposition, and its mass
formula. It DOES NOT assert commutation with the quadratic perturbation
of the closed Legendre operator; the complex graph-domain identification
and polynomial Green formula still need a separate kernel check.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

private theorem eulerianLambdaPos : (0 : ℝ) < 1 / 2 := by norm_num

private theorem eulerianAlphaPos : (0 : ℝ) < 1 / Real.sqrt 2 := by
  positivity

/-- The exact Fock parameter matches the Eulerian Gram coefficient. -/
theorem manuscript14_gram_parameter :
    (1 : ℝ) / (4 * (1 / Real.sqrt 2)) = 1 / Real.sqrt 8 := by
  have hs2 : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hs8 : (Real.sqrt (8 : ℝ)) ^ 2 = 8 :=
    Real.sq_sqrt (by norm_num)
  have hpositive2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hpositive8 : (0 : ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg _
  have hroot : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
    nlinarith
  have hne : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  rw [hroot]
  field_simp [hne]
  nlinarith

/-- The actual bounded complex-Hilbert Gram operator of Manuscript 14.1. -/
noncomputable def manuscript14Gram :
    Lp ℂ 2 (Ultraspherical.measure (1 / 2 : ℝ)) →L[ℂ]
      Lp ℂ 2 (Ultraspherical.measure (1 / 2 : ℝ)) :=
  gram (1 / 2) (1 / Real.sqrt 2) eulerianLambdaPos eulerianAlphaPos

/-- Exact L² integral-kernel interpretation, not merely a formal series. -/
theorem manuscript14Gram_eq_integralLp
    (f : Lp ℂ 2 (Ultraspherical.measure (1 / 2 : ℝ))) :
    manuscript14Gram f =
      gramKernelIntegralLp (1 / 2) (1 / Real.sqrt 2)
        eulerianLambdaPos eulerianAlphaPos f := by
  exact gram_eq_integralLp
    (1 / 2) (1 / Real.sqrt 2) eulerianLambdaPos eulerianAlphaPos f

/-- Genuine operator-norm convergent positive rank-one Gram expansion. -/
theorem manuscript14Gram_eq_nuclear_tsum :
    manuscript14Gram =
      ∑' n : ℕ,
        gramNuclearTerm (1 / 2) (1 / Real.sqrt 2)
          eulerianLambdaPos eulerianAlphaPos n := by
  exact gram_eq_nuclear_tsum
    (1 / 2) (1 / Real.sqrt 2) eulerianLambdaPos eulerianAlphaPos

/-- Its positive nuclear mass is the same scalar as the diagonal
exp(a*u²) integral, with the appropriate ultraspherical probability measure. -/
theorem manuscript14Gram_nuclear_mass_eq_diagonal :
    (∑' n : ℕ, ‖gramNuclearTerm
      (1 / 2) (1 / Real.sqrt 2)
      eulerianLambdaPos eulerianAlphaPos n‖) =
      ∫ u : ℝ, Real.exp (u ^ 2 / (4 * (1 / Real.sqrt 2)))
        ∂(Ultraspherical.measure (1 / 2 : ℝ)) := by
  exact gramNuclearMass_eq_exp_integral
    (1 / 2) (1 / Real.sqrt 2) eulerianLambdaPos eulerianAlphaPos

/-- Kummer's unregularized series for the exact complex L² Gram trace
mass; the required unit-interval Lebesgue identification is separate. -/
theorem manuscript14Gram_nuclear_mass_eq_kummer :
    (∑' n : ℕ, ‖gramNuclearTerm
      (1 / 2) (1 / Real.sqrt 2)
      eulerianLambdaPos eulerianAlphaPos n‖) =
      KummerCoefficients.kummerSeries (1 / 2)
        (1 / (4 * (1 / Real.sqrt 2))) := by
  exact gramNuclearMass_eq_kummerSeries
    (1 / 2) (1 / Real.sqrt 2) eulerianLambdaPos eulerianAlphaPos

#print axioms GegenbauerFock.GeneralUltrasphericalFock.manuscript14_gram_parameter
#print axioms GegenbauerFock.GeneralUltrasphericalFock.manuscript14Gram_eq_integralLp
#print axioms GegenbauerFock.GeneralUltrasphericalFock.manuscript14Gram_eq_nuclear_tsum
#print axioms GegenbauerFock.GeneralUltrasphericalFock.manuscript14Gram_nuclear_mass_eq_diagonal
#print axioms GegenbauerFock.GeneralUltrasphericalFock.manuscript14Gram_nuclear_mass_eq_kummer

end GegenbauerFock.GeneralUltrasphericalFock
