import Mathlib
import SpecialImaginaryPoint.EulerianSinhSeries

/-!
# Manuscript 14.119 — special-value series and asymptotic algebra

The two priority tasks are deliberately separated.

* Proposition 2.1 / Corollary 2.2: genuine analytic series identity at
  a = 1/sqrt(8), plus an exact rational enclosure of sinh(a)/a.
  The latter uses the rigorous exponential Taylor remainder bound in Mathlib.
* Proposition 10.2, display (177): the exact *algebraic* cancellation producing
  coefficients 6, 1/5 and -3/10. These identities are NOT a proof of the
  analytic uniform big-O term; the latter remains a separate obligation.

No numerical oracle, axioms or admitted proofs are used.
-/

namespace SpecialImaginaryPoint.V14119Priorities

/-- Analytic hyperbolic sine at the actual Eulerian point, as the convergent
series of rational numbers in Proposition 2.1. -/
theorem real_special_value_eq_series :
    Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) =
      ∑' n : ℕ, (1 : ℝ) /
        ((8 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ)) := by
  let a : ℝ := 1 / Real.sqrt 8
  have hs : (Real.sqrt (8 : ℝ)) ^ 2 = 8 := by norm_num
  have hnon : Real.sqrt (8 : ℝ) ≠ 0 := by positivity
  have hmul : Real.sqrt 8 * a = 1 := by
    dsimp [a]
    field_simp [hnon]
  have ha2 : a ^ 2 = (1 / 8 : ℝ) := by
    dsimp [a]
    field_simp [hnon]
    nlinarith [hs]
  calc
    Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) =
        Real.sqrt 8 * (∑' n : ℕ,
          a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
      rw [Manuscript14Section11.realSinh_eq_tsum]
    _ = ∑' n : ℕ,
          Real.sqrt 8 * (a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) := by
      rw [tsum_mul_left]
    _ = ∑' n : ℕ, (1 : ℝ) /
          ((8 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ)) := by
      apply tsum_congr
      intro n
      calc
        Real.sqrt 8 * (a ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ)) =
            (Real.sqrt 8 * a) * ((a ^ 2) ^ n) /
              ((2 * n + 1).factorial : ℝ) := by
          rw [pow_add, pow_mul]
          ring
        _ = (1 / 8 : ℝ) ^ n / ((2 * n + 1).factorial : ℝ) := by
          rw [hmul, ha2, one_mul]
        _ = (1 : ℝ) / ((8 : ℝ) ^ n * ((2 * n + 1).factorial : ℝ)) := by
          have h8 : (8 : ℝ) ^ n ≠ 0 := by positivity
          have hfac : ((2 * n + 1).factorial : ℝ) ≠ 0 := by positivity
          rw [div_pow, one_pow]
          field_simp [h8, hfac]

/-- A rigorously certified rational bracket for the actual analytic special
value, not merely for a truncated proxy. This is the bracket used in the
proof of Proposition 10.2 to obtain the Parry index 187. -/
theorem real_special_value_rational_bracket :
    (1020963929 : ℝ) / 10 ^ 9 <
      Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) ∧
    Real.sqrt 8 * Real.sinh (1 / Real.sqrt 8) <
      (1020963930 : ℝ) / 10 ^ 9 := by
  let q : ℝ := Real.sqrt 8
  let u : ℝ := q / 8
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hq2 : q ^ 2 = 8 := by
    dsimp [q]
    norm_num
  have hqle : q ≤ 3 := by
    nlinarith [hq2]
  have hupos : 0 < u := by
    dsimp [u]
    positivity
  have hu_le : u ≤ 1 := by
    dsimp [u]
    linarith
  have huabs : |u| ≤ 1 := by
    rw [abs_of_pos hupos]
    exact hu_le
  have hunegabs : |-u| ≤ 1 := by simpa only [abs_neg] using huabs
  have hu2 : u ^ 2 = (1 / 8 : ℝ) := by
    dsimp [u]
    nlinarith [hq2]
  have hqu : q * u = 1 := by
    dsimp [u]
    nlinarith [hq2]
  have huinv : 1 / q = u := by
    dsimp [u]
    field_simp [hqne]
    nlinarith [hq2]

  let Splus : ℝ := ∑ m ∈ Finset.range 16, u ^ m / (m.factorial : ℝ)
  let Sminus : ℝ := ∑ m ∈ Finset.range 16, (-u) ^ m / (m.factorial : ℝ)
  let E : ℝ := (17 : ℝ) * ((((Nat.factorial 16 : ℕ) : ℝ) * 16)⁻¹)
  have hEnonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hpowle : |u| ^ 16 ≤ (1 : ℝ) :=
    pow_le_one₀ (abs_nonneg _) huabs
  have herror : |u| ^ 16 *
      ((16 + 1 : ℕ) : ℝ) * ((((Nat.factorial 16 : ℕ) : ℝ) * 16)⁻¹) ≤ E := by
    dsimp [E]
    nlinarith [mul_le_mul_of_nonneg_right hpowle
      (show (0 : ℝ) ≤ (17 : ℝ) * ((((Nat.factorial 16 : ℕ) : ℝ) * 16)⁻¹) by positivity)]
  have hplus : |Real.exp u - Splus| ≤ E := by
    have h := Real.exp_bound (x := u) huabs (n := 16) (by norm_num)
    have h' : |Real.exp u - Splus| ≤
        |u| ^ 16 * ((16 + 1 : ℕ) : ℝ) *
          ((((Nat.factorial 16 : ℕ) : ℝ) * 16)⁻¹) := by
      simpa [Splus, div_eq_mul_inv, mul_assoc] using h
    exact h'.trans herror
  have hminus : |Real.exp (-u) - Sminus| ≤ E := by
    have h := Real.exp_bound (x := -u) hunegabs (n := 16) (by norm_num)
    have h' : |Real.exp (-u) - Sminus| ≤
        |u| ^ 16 * ((16 + 1 : ℕ) : ℝ) *
          ((((Nat.factorial 16 : ℕ) : ℝ) * 16)⁻¹) := by
      simpa [Sminus, abs_neg, div_eq_mul_inv, mul_assoc] using h
    exact h'.trans herror
  have hdiff :
      |(Real.exp u - Real.exp (-u)) - (Splus - Sminus)| ≤ 2 * E := by
    rcases abs_le.mp hplus with ⟨hpl, hpu⟩
    rcases abs_le.mp hminus with ⟨hml, hmu⟩
    apply abs_le.mpr
    constructor <;> linarith

  let s7 : ℝ := (2799883227993547921 : ℝ) / 2742391916199936000
  have hpow (k : ℕ) : q * u ^ (2 * k + 1) = (1 / 8 : ℝ) ^ k := by
    calc
      q * u ^ (2 * k + 1) = (q * u) * (u ^ 2) ^ k := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega, pow_add, pow_mul]
        ring
      _ = (1 / 8 : ℝ) ^ k := by rw [hqu, hu2, one_mul]
  have hseven : (q / 2) * (Splus - Sminus) = s7 := by
    have hfinite : (q / 2) * (Splus - Sminus) =
        ∑ k ∈ Finset.range 8,
          (q * u ^ (2 * k + 1)) / ((2 * k + 1).factorial : ℝ) := by
      dsimp [Splus, Sminus]
      norm_num [Finset.sum_range_succ, Nat.factorial]
      ring
    rw [hfinite]
    simp_rw [hpow]
    norm_num [s7, Finset.sum_range_succ, Nat.factorial]
  have hxe :
      |(q * Real.sinh (1 / q)) - s7| ≤ q * E := by
    have heq : q * Real.sinh (1 / q) - s7 =
        (q / 2) * ((Real.exp u - Real.exp (-u)) - (Splus - Sminus)) := by
      rw [huinv, Real.sinh_eq, ← hseven]
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q / 2)]
    calc
      (q / 2) * |(Real.exp u - Real.exp (-u)) - (Splus - Sminus)| ≤
          (q / 2) * (2 * E) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = q * E := by ring
  have hqerr : q * E ≤ 3 * E :=
    mul_le_mul_of_nonneg_right hqle hEnonneg
  have hnumlo :
      (1020963929 : ℝ) / 10 ^ 9 + 3 * E < s7 := by
    norm_num [s7, E, Nat.factorial]
  have hnumhi :
      s7 + 3 * E < (1020963930 : ℝ) / 10 ^ 9 := by
    norm_num [s7, E, Nat.factorial]
  obtain ⟨hl, hh⟩ := abs_le.mp hxe
  constructor <;> dsimp [q] at * <;> linarith

/-- Exact truncated reciprocal-factor identity used in deriving (177).
It is an algebraic component, not the analytic uniform asymptotic. -/
theorem reciprocal_factor_algebra (t : ℝ) (ht : t ≠ 0) :
    (t / 6) * (1 + t / 20) * ((6 / t) * (1 - t / 20)) =
      1 - t ^ 2 / 400 := by
  field_simp [ht]
  ring

/-- The coefficients 6, 1/5 and -3/10 in (177) arise from this exact
cancellation. Here t=x^2 and L=log(6/t); controlling the discarded
analytic remainders is a distinct, still pending task. -/
theorem parry_coefficients_algebra (t L : ℝ) (ht : t ≠ 0) :
    (6 / t) * (1 - t / 20) * (L - t / 20) + (L - t / 20) / 2 =
      (6 / t) * L + L / 5 - 3 / 10 - t / 100 := by
  field_simp [ht]
  ring

#print axioms SpecialImaginaryPoint.V14119Priorities.real_special_value_eq_series
#print axioms SpecialImaginaryPoint.V14119Priorities.real_special_value_rational_bracket
#print axioms SpecialImaginaryPoint.V14119Priorities.reciprocal_factor_algebra
#print axioms SpecialImaginaryPoint.V14119Priorities.parry_coefficients_algebra

end SpecialImaginaryPoint.V14119Priorities
