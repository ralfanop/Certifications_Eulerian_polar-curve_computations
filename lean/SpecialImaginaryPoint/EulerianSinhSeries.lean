import Mathlib

/-!
# The Eulerian hyperbolic-sine parameter as an actual convergent series

This file establishes the analytic bridge from the exact real
hyperbolic sine to the series of *rational* coefficients

  x_E = √2 * sinh(1/√2)
      = ∑ n, 1 / (2^n * (2*n+1)!).

An independent finite-tail bound is needed to deduce the manuscript's
12-decimal strict rational interval in the Lean kernel.
-/

namespace Manuscript14Section11

/-- The real hyperbolic sine agrees with its entire Taylor series.
This follows from the already formalized complex hyperbolic sine
expansion and the real-to-complex embedding. -/
theorem realSinh_eq_tsum (t : ℝ) :
    Real.sinh t =
      ∑' n : ℕ, t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sinh, Complex.ofReal_tsum,
    Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast] using
    (Complex.sinh_eq_tsum (t : ℂ))

/-- The precise real scalar from the Eulerian special point equals
the convergent entirely rational-coefficient series. -/
theorem eulerian_sinh_rational_series :
    Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2) =
      ∑' n : ℕ, (1 : ℝ) /
        ((2 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ)) := by
  let a : ℝ := 1 / Real.sqrt 2
  have hs : (Real.sqrt (2 : ℝ)) ^ 2 = 2 := by norm_num
  have hnon : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hmul : Real.sqrt 2 * a = 1 := by
    dsimp [a]
    field_simp [hnon]
  have ha2 : a ^ 2 = (1 / 2 : ℝ) := by
    dsimp [a]
    field_simp [hnon]
    nlinarith [hs]
  calc
    Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2) =
        Real.sqrt 2 * (∑' n : ℕ,
          a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
      rw [realSinh_eq_tsum]
      rfl
    _ = ∑' n : ℕ,
          Real.sqrt 2 * (a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, (1 : ℝ) /
          ((2 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ)) := by
      apply tsum_congr
      intro n
      calc
        Real.sqrt 2 * (a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) =
            (Real.sqrt 2 * a) * ((a ^ 2) ^ n) /
              ((2 * n + 1).factorial : ℝ) := by
          rw [pow_add, pow_mul]
          ring
        _ = (1 / 2 : ℝ) ^ n / ((2 * n + 1).factorial : ℝ) := by
          rw [hmul, ha2, one_mul]
        _ = (1 : ℝ) / ((2 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ)) := by
          have htwo : (2 : ℝ) ^ n ≠ 0 := by positivity
          have hfac : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
          rw [div_pow, one_pow]
          field_simp [htwo, hfac]

#print axioms Manuscript14Section11.realSinh_eq_tsum
#print axioms Manuscript14Section11.eulerian_sinh_rational_series

end Manuscript14Section11
