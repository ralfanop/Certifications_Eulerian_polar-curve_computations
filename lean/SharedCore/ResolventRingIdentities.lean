import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic

/-! Algebraic resolvent identities in a possibly noncommutative ring. -/

noncomputable section
open scoped Ring

namespace SharedCore.ResolventRingIdentities
variable {R : Type*} [Ring R]

theorem inverse_perturbation_eq (a : R) (ha : IsUnit (1 + a)) :
    -((1 + a)⁻¹ʳ * a) = (1 + a)⁻¹ʳ - 1 := by
  have hc := Ring.inverse_mul_cancel (1 + a) ha
  rw [mul_add, mul_one] at hc
  calc
    -((1 + a)⁻¹ʳ * a) = (1 + a)⁻¹ʳ -
        ((1 + a)⁻¹ʳ + (1 + a)⁻¹ʳ * a) := by abel
    _ = _ := by rw [hc]

theorem inverse_perturbation_product (a : R) (ha : IsUnit (1 + a)) :
    -((1 + a)⁻¹ʳ * a) + a + (-((1 + a)⁻¹ʳ * a)) * a = 0 := by
  rw [inverse_perturbation_eq a ha]
  calc
    _ = (1 + a)⁻¹ʳ * (1 + a) - 1 := by noncomm_ring
    _ = 0 := by rw [Ring.inverse_mul_cancel _ ha, sub_self]

theorem right_resolvent_product (a t : R) (ha : IsUnit (1 + a)) :
    t * (1 + a)⁻¹ʳ + (t * (1 + a)⁻¹ʳ) * a = t := by
  calc
    _ = t * ((1 + a)⁻¹ʳ * (1 + a)) := by noncomm_ring
    _ = t := by rw [Ring.inverse_mul_cancel _ ha, mul_one]

#print axioms inverse_perturbation_eq
#print axioms inverse_perturbation_product
#print axioms right_resolvent_product
end SharedCore.ResolventRingIdentities
