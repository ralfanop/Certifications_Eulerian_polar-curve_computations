import Manuscript15.TerminalLagrangeFiniteCoefficients20261123
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic

/-!
# M15 §6.2: weighted convolution without substitution of Laurent residues

After the verified degree-shift/diagonal identities of PR #524, this is a
separate, unconditional identity that makes the candidate coefficients of
closed Lagrange--Bürmann compatible with the triangular recurrence.

For ψ an arbitrary real formal power series, m > 0 and k ≥ 0:
  (m+k) * [u^(m-1)]((ψ^k)' * ψ^m)
    = k*m * [u^m] ψ^(m+k).
The left side is a genuinely *finite* convolution of coefficients of ψ^k
and ψ^m; the equality is a consequence of the derivative-power identity.

This by itself is not the fixed-point coefficient transfer theorem. The
subsequent step is induction on n in H = X * ψ(H), using this identity and
the certified triangularity of PRs #491 and #524.
-/

namespace Manuscript15.TerminalLagrangeWeighted

open PowerSeries

abbrev P := PowerSeries ℝ

/-- The weighted derivative-power identity behind finite Lagrange inversion.
This is valid for all natural exponents, including k = 0. -/
theorem weighted_derivative (ψ : P) (m k : ℕ) :
    ((m + k : ℕ) : P) *
        ((PowerSeries.derivative (R := ℝ)) (ψ ^ k) * ψ ^ m) =
      (k : P) * ((PowerSeries.derivative (R := ℝ)) (ψ ^ (m + k))) := by
  by_cases hk : k = 0
  · subst k
    simp
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk
  have he : m + k - 1 = m + (k - 1) := by omega
  rw [PowerSeries.derivative_pow, PowerSeries.derivative_pow, he, pow_add]
  push_cast
  ring

/-- Coefficient-level identity: no infinite summation is needed. -/
theorem weighted_coefficient (ψ : P) (m k : ℕ) (hm : 0 < m) :
    ((m + k : ℕ) : ℝ) *
        PowerSeries.coeff (m - 1)
          (((PowerSeries.derivative (R := ℝ)) (ψ ^ k)) * ψ ^ m) =
      ((k : ℝ) * (m : ℝ)) *
        PowerSeries.coeff m (ψ ^ (m + k)) := by
  have h := congrArg (PowerSeries.coeff (m - 1))
    (weighted_derivative ψ m k)
  simp only [PowerSeries.coeff_natCast_mul,
    PowerSeries.coeff_derivative] at h
  have hm' : m - 1 + 1 = m := by omega
  rw [hm'] at h
  push_cast at h
  convert h using 1 <;> ring

/-- The weighted finite Cauchy convolution, indexed by the antidiagonal.
This is the key identity required to prove that Lagrange--Bürmann's
candidate coefficients satisfy the inverse-series recurrence. -/
theorem weighted_finite_convolution (ψ : P) (m k : ℕ) (hm : 0 < m) :
    ((m + k : ℕ) : ℝ) *
        (∑ p ∈ Nat.antidiagonal (m - 1),
          (PowerSeries.coeff (p.1 + 1) (ψ ^ k) * ((p.1 + 1 : ℕ) : ℝ)) *
            PowerSeries.coeff p.2 (ψ ^ m)) =
      ((k : ℝ) * (m : ℝ)) *
        PowerSeries.coeff m (ψ ^ (m + k)) := by
  simpa only [PowerSeries.coeff_mul, PowerSeries.coeff_derivative]
    using weighted_coefficient ψ m k hm

#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_derivative
#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_coefficient
#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_finite_convolution

end Manuscript15.TerminalLagrangeWeighted
