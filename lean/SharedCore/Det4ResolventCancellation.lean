import Mathlib

/-!
Shared 11–16 core: exact algebraic cancellation underlying the fourth
regularized Fredholm logarithmic derivative.  This is a *finite algebraic*
bridge, not a trace-class, operator-resolvent, or det₄ theorem.
-/

namespace SharedCore.SchattenFredholm

/-- The scalar fourth-order regularized resolvent cancellation, valid
away from both poles.  No analytic continuation is used. -/
theorem det4_resolvent_cancellation (a z : ℂ)
    (ha : a ≠ 0) (haz : a + z ≠ 0) :
    1 / (a + z) - 1 / a + z / a ^ 2 - z ^ 2 / a ^ 3 =
      -(z ^ 3) / (a ^ 3 * (a + z)) := by
  field_simp
  ring

/-- Finite spectral multiplicities may be inserted without changing
the exact cancellation.  Passing to infinite sums requires a separate
summability and differentiation argument. -/
theorem det4_finite_spectral_cancellation {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (m : ι → ℂ) (z : ℂ)
    (ha : ∀ i ∈ s, a i ≠ 0)
    (haz : ∀ i ∈ s, a i + z ≠ 0) :
    (∑ i ∈ s, m i *
      (1 / (a i + z) - 1 / a i + z / (a i) ^ 2 -
        z ^ 2 / (a i) ^ 3)) =
    ∑ i ∈ s, -(m i * z ^ 3) / ((a i) ^ 3 * (a i + z)) := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [det4_resolvent_cancellation (a i) z (ha i hi) (haz i hi)]
  ring

#print axioms SharedCore.SchattenFredholm.det4_resolvent_cancellation
#print axioms SharedCore.SchattenFredholm.det4_finite_spectral_cancellation
end SharedCore.SchattenFredholm
