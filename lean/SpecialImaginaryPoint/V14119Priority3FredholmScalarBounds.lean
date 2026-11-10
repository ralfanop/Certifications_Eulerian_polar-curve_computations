import Mathlib

/-!
# Priority 3 — dimension-independent scalar exponential envelope

These lemmas are scalar ingredients in the eventual complex Gram–Hadamard
Fredholm determinant perturbation argument. For arbitrary nonnegative
nuclear costs c_i, the combinatorial product bound

  ∏_{i∈s} (1 + r*c_i) ≤ exp (r * ∑_{i∈s} c_i)

holds for r ≥ 0 without any dimension-dependent factor.
The increment also obeys

  ∏(1 + r*c_i) - 1 ≤ (r * ∑ c_i) * exp (r * ∑ c_i).

A future module must *separately* prove that the finite Gram-determinant
expansion is dominated by precisely these scalar products. None of the
lemmas here asserts the Gram–Hadamard inequality or a universal Fredholm
determinant on CFC S₁.
-/

noncomputable section

namespace Manuscript14Priority3.FredholmScalarBounds

/-- Dimension-free exponential majorant for a finite product of
positive nuclear-cost factors. -/
theorem finite_nuclear_product_le_exp
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∏ i ∈ s, (1 + r * c i)) ≤
      Real.exp (r * ∑ i ∈ s, c i) := by
  calc
    (∏ i ∈ s, (1 + r * c i)) ≤
        ∏ i ∈ s, Real.exp (r * c i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact add_nonneg (by norm_num) (mul_nonneg hr (hc i hi))
      · intro i hi
        simpa only [add_comm] using Real.add_one_le_exp (r * c i)
    _ = Real.exp (r * ∑ i ∈ s, c i) := by
      rw [← Real.exp_sum, Finset.mul_sum]

/-- Elementary exponential increment inequality, valid for
every real x (not just x ≥ 0). -/
theorem exp_sub_one_le_mul_exp (x : ℝ) :
    Real.exp x - 1 ≤ x * Real.exp x := by
  have hbase : 1 - x ≤ Real.exp (-x) := by
    nlinarith [Real.add_one_le_exp (-x)]
  have h := mul_le_mul_of_nonneg_right hbase
    (le_of_lt (Real.exp_pos x))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  nlinarith

/-- Dimension-free bound on the nonconstant part of the nuclear-cost
product. This is the scalar factor that appears when at least one
perturbation rank-one term is selected in a Fredholm expansion. -/
theorem finite_nuclear_product_increment_le
    {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (r : ℝ) (hr : 0 ≤ r)
    (hc : ∀ i ∈ s, 0 ≤ c i) :
    (∏ i ∈ s, (1 + r * c i)) - 1 ≤
      (r * ∑ i ∈ s, c i) *
        Real.exp (r * ∑ i ∈ s, c i) := by
  have hprod := finite_nuclear_product_le_exp s c r hr hc
  have hexp := exp_sub_one_le_mul_exp
    (r * ∑ i ∈ s, c i)
  linarith

#print axioms Manuscript14Priority3.FredholmScalarBounds.finite_nuclear_product_le_exp
#print axioms Manuscript14Priority3.FredholmScalarBounds.exp_sub_one_le_mul_exp
#print axioms Manuscript14Priority3.FredholmScalarBounds.finite_nuclear_product_increment_le

end Manuscript14Priority3.FredholmScalarBounds
