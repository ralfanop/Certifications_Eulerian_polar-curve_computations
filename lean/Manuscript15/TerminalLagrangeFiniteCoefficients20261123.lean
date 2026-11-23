import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-!
# Manuscript 15, Section 6.2: coefficientwise reversion (finite route)

An independent route toward the closed Lagrange--Bürmann formula.  We
begin with a genuine all-order coefficient identity in the ordinary
power-series ring, without using the Laurent residue substitution theorem.

If H = X * Q, then H^k = X^k * Q^k.  Consequently the coefficient of
degree n+k of H^k is the coefficient of degree n of Q^k.  In particular
H^k has no coefficient below k, and its diagonal coefficient is
(coeff 0 Q)^k.  These identities supply the triangularity and the
nonvanishing diagonal required for coefficientwise reversion.

For the eventual application Q = (phi^{-1}).subst H, where
H = X * (phi^{-1}).subst H and phi(0) is nonzero.  The full
Lagrange--Bürmann coefficient formula requires an additional identity,
namely the transfer of coefficients from Q^k to (phi^{-1})^n.
That identity is NOT claimed or assumed in this module.
-/

namespace Manuscript15.TerminalLagrangeFinite

open PowerSeries

abbrev P := PowerSeries ℝ

/-- Exact degree-shift identity for all natural powers. -/
theorem coeff_factored_power (H Q : P)
    (hH : H = PowerSeries.X * Q) (n k : ℕ) :
    PowerSeries.coeff (n + k) (H ^ k) =
      PowerSeries.coeff n (Q ^ k) := by
  rw [hH, mul_pow]
  exact PowerSeries.coeff_X_pow_mul (Q ^ k) k n

/-- Every coefficient below the power k vanishes, without analytic assumptions. -/
theorem coeff_factored_below (H Q : P)
    (hH : H = PowerSeries.X * Q) (n k : ℕ) (hn : n < k) :
    PowerSeries.coeff n (H ^ k) = 0 := by
  rw [hH, mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [Nat.not_le.mpr hn]

/-- The degree-k diagonal of H^k is the k-th power of the linear coefficient. -/
theorem coeff_factored_diagonal (H Q : P)
    (hH : H = PowerSeries.X * Q) (k : ℕ) :
    PowerSeries.coeff k (H ^ k) =
      (PowerSeries.coeff 0 Q) ^ k := by
  have h := coeff_factored_power H Q hH 0 k
  simpa only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_pow] using h

/-- The first coefficient of H is the constant coefficient of Q. -/
theorem coeff_factored_linear (H Q : P)
    (hH : H = PowerSeries.X * Q) :
    PowerSeries.coeff 1 H = PowerSeries.coeff 0 Q := by
  simpa only [pow_one, zero_add] using
    coeff_factored_power H Q hH 0 1

/-- Nonzero constant coefficient gives a nonvanishing diagonal in every degree. -/
theorem coeff_factored_diagonal_ne_zero (H Q : P)
    (hH : H = PowerSeries.X * Q) (hQ : PowerSeries.coeff 0 Q ≠ 0)
    (k : ℕ) :
    PowerSeries.coeff k (H ^ k) ≠ 0 := by
  rw [coeff_factored_diagonal H Q hH]
  exact pow_ne_zero k hQ


/-- The shifted coefficient identity for the *actual implicit fixed-point equation*
    H = X * ψ(H), with substitution in the ordinary power-series ring. -/
theorem fixedpoint_coeff_shift (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ) (n k : ℕ) :
    PowerSeries.coeff (n + k) (H ^ k) =
      PowerSeries.coeff n ((PowerSeries.subst H ψ) ^ k) :=
  coeff_factored_power H (PowerSeries.subst H ψ) hH n k

/-- A solution of H = X * ψ(H) necessarily has zero constant coefficient. -/
theorem fixedpoint_constantCoeff_zero (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ) :
    PowerSeries.constantCoeff H = 0 := by
  rw [hH]
  simp

/-- The diagonal n = k case of closed Lagrange inversion, now for the
    actual fixed-point equation rather than an arbitrary factorisation. -/
theorem fixedpoint_diagonal (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ) (k : ℕ) :
    PowerSeries.coeff k (H ^ k) = PowerSeries.coeff 0 (ψ ^ k) := by
  have h0 := fixedpoint_constantCoeff_zero H ψ hH
  have hs : PowerSeries.constantCoeff (PowerSeries.subst H ψ) =
      PowerSeries.constantCoeff ψ := by
    simpa using
      (PowerSeries.constantCoeff_subst_of_constantCoeff_zero
        (R := ℝ) (S := ℝ) (a := H) h0 ψ)
  rw [coeff_factored_diagonal H (PowerSeries.subst H ψ) hH]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, hs, map_pow]

#print axioms Manuscript15.TerminalLagrangeFinite.coeff_factored_power
#print axioms Manuscript15.TerminalLagrangeFinite.coeff_factored_below
#print axioms Manuscript15.TerminalLagrangeFinite.coeff_factored_diagonal
#print axioms Manuscript15.TerminalLagrangeFinite.coeff_factored_linear
#print axioms Manuscript15.TerminalLagrangeFinite.coeff_factored_diagonal_ne_zero
#print axioms Manuscript15.TerminalLagrangeFinite.fixedpoint_coeff_shift
#print axioms Manuscript15.TerminalLagrangeFinite.fixedpoint_constantCoeff_zero
#print axioms Manuscript15.TerminalLagrangeFinite.fixedpoint_diagonal

end Manuscript15.TerminalLagrangeFinite
