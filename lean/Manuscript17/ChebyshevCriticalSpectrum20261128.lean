import Mathlib

noncomputable section
namespace Manuscript17.ChebyshevCriticalSpectrum

open Polynomial Polynomial.Chebyshev

/-! Actual critical-value and second-derivative classification for arbitrary
positive order. No assumptions about roots, factorization or Jordan form.
The passage to matrix Jordan blocks is a separate obligation. -/

def fiber (m : ℤ) (w : ℂ) : ℂ[X] := T ℂ m - C w

theorem fiber_eval (m : ℤ) (w z : ℂ) :
    (fiber m w).eval z = (T ℂ m).eval z - w := by
  simp [fiber]

theorem derivative_fiber (m : ℤ) (w : ℂ) :
    derivative (fiber m w) = derivative (T ℂ m) := by
  simp [fiber]

theorem critical_value_sq (m : ℤ) (hm : m ≠ 0) (z : ℂ)
    (hd : (derivative (T ℂ m)).eval z = 0) :
    ((T ℂ m).eval z)^2 = 1 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hU : (U ℂ (m-1)).eval z = 0 := by
    rw [T_derivative_eq_U] at hd
    have h : (m : ℂ) * (U ℂ (m-1)).eval z = 0 := by
      simpa using hd
    exact (mul_eq_zero.mp h).resolve_left hmC
  obtain ⟨θ, rfl⟩ := Complex.cos_surjective z
  have hs := U_complex_cos θ (m-1)
  rw [hU, zero_mul, Int.cast_sub, Int.cast_one, sub_add_cancel] at hs
  rw [T_complex_cos]
  have h := Complex.sin_sq_add_cos_sq ((m:ℂ)*θ)
  rw [← hs, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add] at h
  exact h

theorem critical_value (m : ℤ) (hm : m ≠ 0) (z : ℂ)
    (hd : (derivative (T ℂ m)).eval z = 0) :
    (T ℂ m).eval z = 1 ∨ (T ℂ m).eval z = -1 := by
  have h := critical_value_sq m hm z hd
  have hprod : ((T ℂ m).eval z - 1) * ((T ℂ m).eval z + 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hprod with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h2)

theorem critical_second_derivative_ne_zero (m : ℤ) (hm : m ≠ 0) (z : ℂ)
    (hd : (derivative (T ℂ m)).eval z = 0) :
    (derivative (derivative (T ℂ m))).eval z ≠ 0 := by
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hw : (T ℂ m).eval z ≠ 0 := by
    rcases critical_value m hm z hd with h | h <;> rw [h] <;> norm_num
  have h := one_sub_X_sq_mul_iterate_derivative_T_eval (R := ℂ) m 0 z
  intro hzero
  change (1-z^2) * (derivative (derivative (T ℂ m))).eval z =
    (2*((0:ℕ):ℂ)+1)*z*(derivative (T ℂ m)).eval z -
      ((m:ℂ)^2-((0:ℕ):ℂ)^2)*(T ℂ m).eval z at h
  rw [hzero, hd] at h
  exact (mul_ne_zero (pow_ne_zero 2 hmC) hw) (by
    linear_combination h)

theorem noncritical_fiber_derivative (m : ℤ) (hm : m ≠ 0) (w z : ℂ)
    (hw1 : w ≠ 1) (hw2 : w ≠ -1) (hz : (fiber m w).eval z = 0) :
    (derivative (fiber m w)).eval z ≠ 0 := by
  rw [derivative_fiber]
  intro hd
  have he : (T ℂ m).eval z = w := sub_eq_zero.mp (by simpa [fiber] using hz)
  rcases critical_value m hm z hd with h | h
  · exact hw1 (he.symm.trans h)
  · exact hw2 (he.symm.trans h)

theorem fiber_no_triple_derivative_zero (m : ℤ) (hm : m ≠ 0) (w z : ℂ)
    (hd : (derivative (fiber m w)).eval z = 0) :
    (derivative (derivative (fiber m w))).eval z ≠ 0 := by
  rw [derivative_fiber] at hd ⊢
  exact critical_second_derivative_ne_zero m hm z hd

#print axioms fiber_eval
#print axioms derivative_fiber
#print axioms critical_value_sq
#print axioms critical_value
#print axioms critical_second_derivative_ne_zero
#print axioms noncritical_fiber_derivative
#print axioms fiber_no_triple_derivative_zero

end Manuscript17.ChebyshevCriticalSpectrum
