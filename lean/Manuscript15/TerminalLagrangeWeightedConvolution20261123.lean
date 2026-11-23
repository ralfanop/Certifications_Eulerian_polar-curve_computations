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


/-- Substitution has an exact *finite* coefficient expansion when the
inner series H has zero constant term. The bound j ≤ m follows from
H = X * ψ(H), without any analytic convergence assumption. -/
theorem fixedpoint_subst_finite (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (m k : ℕ) :
    PowerSeries.coeff m ((PowerSeries.subst H ψ) ^ k) =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff j (ψ ^ k) * PowerSeries.coeff m (H ^ j) := by
  have h0 := Manuscript15.TerminalLagrangeFinite.fixedpoint_constantCoeff_zero H ψ hH
  have hs : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' h0
  rw [← PowerSeries.subst_pow hs ψ k, PowerSeries.coeff_subst' hs]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (m + 1))]
  · simp only [smul_eq_mul]
  · intro j hj
    by_contra hj'
    have hjgt : m < j := by
      have hn : ¬ j < m + 1 := by
        intro hlt
        exact hj' (Finset.mem_range.mpr hlt)
      omega
    have hz : PowerSeries.coeff m (H ^ j) = 0 :=
      Manuscript15.TerminalLagrangeFinite.coeff_factored_below
        H (PowerSeries.subst H ψ) hH m j hjgt
    have hzero :
        PowerSeries.coeff j (ψ ^ k) • PowerSeries.coeff m (H ^ j) = 0 := by
      simp [hz]
    exact (Function.mem_support.mp hj) hzero

/-- A true *finite* triangular recurrence for powers of the implicit
solution H = X * ψ(H), valid uniformly in m and k. -/
theorem fixedpoint_power_finite_sum (H ψ : P)
    (hH : H = PowerSeries.X * PowerSeries.subst H ψ)
    (m k : ℕ) :
    PowerSeries.coeff (m + k) (H ^ k) =
      ∑ j ∈ Finset.range (m + 1),
        PowerSeries.coeff j (ψ ^ k) * PowerSeries.coeff m (H ^ j) := by
  rw [Manuscript15.TerminalLagrangeFinite.fixedpoint_coeff_shift H ψ hH m k]
  exact fixedpoint_subst_finite H ψ hH m k

#print axioms Manuscript15.TerminalLagrangeWeighted.fixedpoint_subst_finite
#print axioms Manuscript15.TerminalLagrangeWeighted.fixedpoint_power_finite_sum

#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_derivative
#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_coefficient
#print axioms Manuscript15.TerminalLagrangeWeighted.weighted_finite_convolution

end Manuscript15.TerminalLagrangeWeighted
