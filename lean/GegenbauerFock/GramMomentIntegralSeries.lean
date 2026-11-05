import GegenbauerFock.AdjointPolynomial

/-!
# V007: integral-kernel Gram expansion in the actual source L² space

This is the full nontruncated Gram operator expressed as a norm-
convergent infinite sum of L² monomials with genuine scalar Bochner
moment integrals. It is a rigorous kernel-series realization.
The later conversion of this L² series into one exponential integral
under the μ-a.e. identification is tracked separately.
-/

open MeasureTheory
open scoped InnerProduct

namespace GegenbauerFock.GeneralUltrasphericalFock

/-- Actual Gram operator as an L²-norm-convergent sum with true
integral moments and exact conjugated Fourier-row amplitudes. -/
theorem gram_moment_integral_series
    (lam alpha : ℝ) (hlam : 0 < lam) (ha : 0 < alpha)
    (f : Lp ℂ 2 (Ultraspherical.measure lam)) :
    gram lam alpha hlam ha f =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ,
        (((star (WeightedMoments.complexWeight alpha n) *
            WeightedMoments.complexWeight alpha n) *
            (∫ v : ℝ, (v : ℂ) ^ n * f v
              ∂(Ultraspherical.measure lam))) •
          WeightedMoments.monomial
            (Ultraspherical.measure lam) (ae_abs_le_one lam) n) := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [gram_eq_tsum_rows lam alpha hlam ha f]
  apply tsum_congr
  intro n
  rw [AdjointPolynomial.coefficient_adjoint_explicit
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n]
  rw [WeightedMoments.coefficient_integral
    (Ultraspherical.measure lam) (ae_abs_le_one lam) alpha n f]
  congr 1
  ring

#print axioms GegenbauerFock.GeneralUltrasphericalFock.gram_moment_integral_series

end GegenbauerFock.GeneralUltrasphericalFock
