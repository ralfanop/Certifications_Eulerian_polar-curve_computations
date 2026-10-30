import EulerianGrothendieck.BernoulliCumulantIdentification
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! # Task F, part 2: the zeta form of the uniform log-coefficients

Separately from the Bernoulli identification, Euler's evaluation of `ζ(2j)` (Mathlib's
`riemannZeta_two_mul_nat`) gives, for every `j ≥ 1`,
`a_j = (-1)^{j-1} 3^j ζ(2j)/(j π^{2j})`, and hence
`standardUniformCumulant (j-1) = (-1)^{j-1} 3^j ζ(2j)/π^{2j}`. -/

noncomputable section
open scoped BigOperators Nat
open Complex
namespace EulerianGrothendieck

theorem uniformLogCoefficient_zeta (j : ℕ) (hj : 1 ≤ j) :
    (uniformLogCoefficient j : ℂ) =
      (-1) ^ (j-1) * 3 ^ j * riemannZeta (2 * j) / (j * (Real.pi : ℂ) ^ (2 * j)) := by
  have hpi : (Real.pi : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hfac : (((2 * j) ! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have hsign : ((-1 : ℂ) ^ (j-1)) * (-1) ^ (j+1) = 1 := by
    rw [← pow_add, show j - 1 + (j + 1) = 2 * j by omega, pow_mul]; norm_num
  calc (uniformLogCoefficient j : ℂ)
      = ((-1 : ℂ) ^ (j-1) * (-1) ^ (j+1)) *
          (3 ^ j * 2 ^ (2*j-1) * (Real.pi : ℂ) ^ (2*j) * (bernoulli (2*j) : ℂ) /
            ((((2*j) ! : ℕ) : ℂ) * (j * (Real.pi : ℂ) ^ (2*j)))) := by
        rw [hsign, one_mul, uniformLogCoefficient]
        push_cast
        rw [div_eq_div_iff (mul_ne_zero hj0 hfac) (mul_ne_zero hfac (mul_ne_zero hj0 hpi))]
        ring
    _ = (-1) ^ (j-1) * 3 ^ j * riemannZeta (2 * j) / (j * (Real.pi : ℂ) ^ (2 * j)) := by
        rw [riemannZeta_two_mul_nat (by omega)]
        ring

/-- `standardUniformCumulant (j-1) = (-1)^{j-1} 3^j ζ(2j)/π^{2j}` for every `j ≥ 1`. -/
theorem standardUniformCumulant_zeta (j : ℕ) (hj : 1 ≤ j) :
    (standardUniformCumulant (j-1) : ℂ) =
      (-1) ^ (j-1) * 3 ^ j * riemannZeta (2 * j) / (Real.pi : ℂ) ^ (2 * j) := by
  rw [standardUniformCumulant_eq_mul_logCoefficient j hj]
  push_cast
  rw [uniformLogCoefficient_zeta j hj]
  have hj0 : (j : ℂ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  have hpi : (Real.pi : ℂ) ^ (2 * j) ≠ 0 := pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero)
  field_simp

end EulerianGrothendieck
