/-
# V478 §3.11: the Montgomery–Taylor constants and the point z₀ = i/√2 of Eq. (4)

The manuscript states that, with `z₀ = i/√2` (the parameter of Eq. (4)),
`z₀ coth z₀ = (1/√2) cot(1/√2)`, so that the Montgomery–Taylor constant is
`C_MT = 1/2 + z₀ coth z₀` and the proportion of simple zeros on the critical line is
`3/2 - z₀ coth z₀` (Lamzouri, arXiv:2609.02882v2, Eqs. (1.1), (3.1)).

`z0_coth_z0` proves the identity; the printed decimals 1.3274992963… and 0.6725007… are certified
by interval arithmetic in `numerics/montgomery_taylor.py`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace EulerianCert.MontgomeryTaylor

open Complex

/-- `z coth z = x cot x` for `z = x i`, `x` real; with `x = 1/√2` this is the identity of §3.11. -/
theorem coth_imaginary (x : ℝ) :
    ((x : ℂ) * I) * Complex.cosh ((x : ℂ) * I) / Complex.sinh ((x : ℂ) * I)
      = ((x * Real.cos x / Real.sin x : ℝ) : ℂ) := by
  rw [Complex.cosh_mul_I, Complex.sinh_mul_I]
  push_cast
  rw [mul_div_assoc, mul_div_assoc]
  by_cases h : Complex.sin (x : ℂ) = 0
  · simp [h]
  · field_simp

/-- §3.11: `z₀ coth z₀ = (1/√2) cot(1/√2)` for `z₀ = i/√2`. -/
theorem z0_coth_z0 :
    ((1 / Real.sqrt 2 : ℝ) * I) * Complex.cosh ((1 / Real.sqrt 2 : ℝ) * I)
        / Complex.sinh ((1 / Real.sqrt 2 : ℝ) * I)
      = (((1 / Real.sqrt 2) * Real.cos (1 / Real.sqrt 2) / Real.sin (1 / Real.sqrt 2) : ℝ) : ℂ) :=
  coth_imaginary (1 / Real.sqrt 2)

end EulerianCert.MontgomeryTaylor
