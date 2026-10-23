import V033GramExpansion
import V033RationalRemainder

noncomputable section
namespace V033.UniformSum
open Polynomial

def recurrenceNumerator (j : ℕ) := determinantPolynomial (j+2)*determinantPolynomial j
def recurrenceDenominator (j : ℕ) := determinantPolynomial (j+1)^2

theorem product_constant (p q : ℝ[X]) : (p*q).coeff 0 = p.coeff 0*q.coeff 0 := by
  rw [coeff_mul]
  simp

theorem recurrence_constant_identity (j : ℕ) :
    (recurrenceNumerator j).coeff 0 = (j+1:ℝ)*(recurrenceDenominator j).coeff 0 := by
  rw [recurrenceNumerator, recurrenceDenominator, pow_two, product_constant,
    product_constant, determinant_constant, determinant_constant, determinant_constant,
    gaussianDeterminant_succ, gaussianDeterminant_succ, Nat.factorial_succ]
  push_cast
  ring

theorem recurrence_linear_identity (j : ℕ) :
    (recurrenceNumerator j).coeff 1 =
      (-(3/5:ℝ)*(j+1)*j)*(recurrenceDenominator j).coeff 0 +
      (j+1:ℝ)*(recurrenceDenominator j).coeff 1 := by
  rw [recurrenceNumerator, recurrenceDenominator, pow_two, Jet.mul_coeff_one,
    Jet.mul_coeff_one, product_constant]
  simp only [determinant_constant, determinant_linear]
  rw [gaussianDeterminant_succ, gaussianDeterminant_succ, Nat.factorial_succ]
  push_cast
  ring

theorem recurrence_denominator_nonzero (j : ℕ) :
    (recurrenceDenominator j).coeff 0 ≠ 0 := by
  rw [recurrenceDenominator, pow_two, product_constant, determinant_constant]
  exact mul_ne_zero (ne_of_gt (gaussianDeterminant_pos _))
    (ne_of_gt (gaussianDeterminant_pos _))

/-- All degrees, with an established O(M^-2) remainder in the normalized variable. -/
theorem normalized_determinant_remainder (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ M : ℕ, N ≤ M →
      (recurrenceDenominator j).eval (1/(M:ℝ)) ≠ 0 ∧
      |(recurrenceNumerator j).eval (1/(M:ℝ)) /
          (recurrenceDenominator j).eval (1/(M:ℝ)) -
        ((j+1:ℝ) - (3/5:ℝ)*(j+1)*j/(M:ℝ))| ≤ C/(M:ℝ)^2 := by
  simpa only [neg_mul, neg_div, add_neg_cancel_left, sub_eq_add_neg] using
    V033.rational_remainder_bound _ _ (j+1:ℝ) (-(3/5:ℝ)*(j+1)*j)
      (recurrence_denominator_nonzero j) (recurrence_constant_identity j)
      (recurrence_linear_identity j)

/-- All-degree O(M^-1) estimate after restoring the variance M/12. -/
theorem original_scale_determinant_remainder (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 0 < N ∧ ∀ M : ℕ, N ≤ M →
      (recurrenceDenominator j).eval (1/(M:ℝ)) ≠ 0 ∧
      |((M:ℝ)/12)*((recurrenceNumerator j).eval (1/(M:ℝ)) /
          (recurrenceDenominator j).eval (1/(M:ℝ))) -
        ((j+1:ℝ)*M/12 - (j+1:ℝ)*j/20)| ≤ C/(M:ℝ) := by
  obtain ⟨C,hC,N,hN⟩ := normalized_determinant_remainder j
  refine ⟨C/12, by positivity, max N 1, by omega, ?_⟩
  intro M hM
  obtain ⟨hd,hb⟩ := hN M (by omega)
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hmn := ne_of_gt hm
  refine ⟨hd, ?_⟩
  rw [show ((M:ℝ)/12)*((recurrenceNumerator j).eval (1/(M:ℝ)) /
          (recurrenceDenominator j).eval (1/(M:ℝ))) -
        ((j+1:ℝ)*M/12 - (j+1:ℝ)*j/20) =
      ((M:ℝ)/12) * (((recurrenceNumerator j).eval (1/(M:ℝ)) /
          (recurrenceDenominator j).eval (1/(M:ℝ))) -
        ((j+1:ℝ) - (3/5:ℝ)*(j+1)*j/(M:ℝ))) by field_simp; ring]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ)<M/12)]
  calc
    _ ≤ ((M:ℝ)/12)*(C/(M:ℝ)^2) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (C/12)/(M:ℝ) := by field_simp

#print axioms original_scale_determinant_remainder
end V033.UniformSum
