import GegenbauerFock.GeneralUltrasphericalFock
import GegenbauerFock.SummableRowsCompact

/-!
# V007 exact row energy formula for the concrete ultraspherical Fock operator

This is an exact, infinite-dimensional coefficient-space Hilbert-Schmidt
row-energy identity for the actual operator C into ℓ²(ℕ;ℂ).
It uses the canonical output basis and identifies each squared row norm
with (1/(4α))ⁿ/n! times the L² norm squared of the monomial uⁿ.

By definition, the row energy is the Hilbert-Schmidt energy associated
with the canonical output orthonormal basis. The equivalence with
the Hilbert-Schmidt ideal norm and the hypergeometric integral
requires further formal development.
-/

open MeasureTheory

namespace GegenbauerFock.GeneralUltrasphericalFock

noncomputable def rowEnergy (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) : ℝ :=
  ∑' n : ℕ, ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2

/-- Exact individual row-energy identity for the real ultraspherical
measure, including the normalization of the coherent coefficients. -/
theorem row_norm_sq_formula (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) (n : ℕ) :
    ‖SummableRowsCompact.row (C lam alpha hlam ha) n‖ ^ 2 =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      WeightedMoments.squareWeight alpha n *
        ‖WeightedMoments.monomial (Ultraspherical.measure lam)
          (ae_abs_le_one lam) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  rw [C_row_eq]
  unfold WeightedMoments.coefficient
  rw [norm_smul, innerSL_apply_norm, mul_pow]
  rw [WeightedMoments.complexWeight_norm_sq alpha ha n]

/-- Exact infinite row-energy identity in the coefficient Hilbert model. -/
theorem rowEnergy_eq (lam alpha : ℝ)
    (hlam : 0 < lam) (ha : 0 < alpha) :
    rowEnergy lam alpha hlam ha =
      letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
        Ultraspherical.probability lam hlam
      ∑' n : ℕ, WeightedMoments.squareWeight alpha n *
        ‖WeightedMoments.monomial (Ultraspherical.measure lam)
          (ae_abs_le_one lam) n‖ ^ 2 := by
  letI : IsProbabilityMeasure (Ultraspherical.measure lam) :=
    Ultraspherical.probability lam hlam
  unfold rowEnergy
  apply tsum_congr
  intro n
  exact row_norm_sq_formula lam alpha hlam ha n

#print axioms GegenbauerFock.GeneralUltrasphericalFock.row_norm_sq_formula
#print axioms GegenbauerFock.GeneralUltrasphericalFock.rowEnergy_eq

end GegenbauerFock.GeneralUltrasphericalFock
