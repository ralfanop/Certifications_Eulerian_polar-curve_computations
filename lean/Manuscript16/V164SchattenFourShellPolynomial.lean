import Mathlib

/-!
Manuscript 16 v16.4, Section 13.
Exact polynomial comparison underlying the fourth-power nearest-mode
spectral-shell estimate. This is a single algebraic obligation, NOT a
Schatten-class theorem, infinite-series proof, or Arb certificate.
Authoritative ZIP SHA256:
c6e92c8a6a58504f41fb1756be20e9be66739fb9880b00a34012718b46d2586f
-/

namespace Manuscript16

/-- The exact numerator comparison for the fourth-power shell:
x²(x²−1) ≤ (x+1)⁴ when x≥2. -/
theorem schatten_four_shell_polynomial (x : ℝ) (hx : 2 ≤ x) :
    x ^ 2 * (x ^ 2 - 1) ≤ (x + 1) ^ 4 := by
  have h0 : 0 ≤ x := by linarith
  have h2 : 0 ≤ x ^ 2 := pow_nonneg h0 _
  have h3 : 0 ≤ x ^ 3 := pow_nonneg h0 _
  nlinarith

#print axioms Manuscript16.schatten_four_shell_polynomial

end Manuscript16
