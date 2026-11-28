import Mathlib
open Filter Topology
noncomputable section
namespace Manuscript14V14122Bernoulli

/-- The convention in v14.122 is Mathlib's positive-B1 convention. -/
theorem convention : bernoulli' 0 = 1 ∧ bernoulli' 1 = 1 / 2 :=
  ⟨bernoulli'_zero, bernoulli'_one⟩

theorem polynomial_one (t : ℚ) :
    (Polynomial.bernoulli 1).eval t =
      bernoulli' 0 * (t - 1) + bernoulli' 1 := by
  rw [Polynomial.bernoulli_one, bernoulli'_zero, bernoulli'_one]
  simp
  ring

theorem polynomial_endpoint :
    (Polynomial.bernoulli 1).eval 1 = bernoulli' 1 :=
  Polynomial.bernoulli_eval_one 1

/-- Removable value at zero; elsewhere use the actual Riemann zeta. -/
def bernoulliFunction (s : ℂ) : ℂ :=
  if s = 0 then 1 else -s * riemannZeta (1 - s)

theorem function_zero : bernoulliFunction 0 = 1 := by simp [bernoulliFunction]

theorem function_one : bernoulliFunction 1 = (1 : ℂ) / 2 := by
  simp [bernoulliFunction, riemannZeta_zero]

theorem interpolation (k : ℕ) :
    bernoulliFunction ((k : ℂ) + 1) = (bernoulli' (k + 1) : ℂ) := by
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [bernoulliFunction, if_neg hk, show (1 : ℂ) - ((k : ℂ) + 1) = -(k : ℂ) by ring,
    riemannZeta_neg_nat_eq_bernoulli']
  push_cast
  field_simp [hk] <;> ring

/-- The quartic uses the actual two Mathlib Bernoulli numbers. -/
theorem quartic (x : ℚ) :
    x^4 - x^2 / 2 + 1 / 32 =
      bernoulli' 0 * x^4 - bernoulli' 1 * (x^2 - (bernoulli' 1)^4) := by
  rw [bernoulli'_zero, bernoulli'_one]
  ring

/-- Discriminant formula evaluated on the prescribed scaled quartic. -/
theorem discriminant_family (s A C : ℝ)
    (hA : A = -(s^2 / 2)) (hC : C = s^4 / 32) :
    16*C*(4*C-A^2)^2 = s^12 / 128 := by
  rw [hA,hC]
  ring

theorem discriminant_monic : (16:ℚ)*(1/32)*(4*(1/32)-(1/2)^2)^2 = 1/128 := by
  norm_num

#print axioms convention
#print axioms polynomial_one
#print axioms polynomial_endpoint
#print axioms function_zero
#print axioms function_one
#print axioms interpolation
#print axioms quartic
#print axioms discriminant_family
#print axioms discriminant_monic
end Manuscript14V14122Bernoulli
