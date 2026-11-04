import Mathlib
import SpecialImaginaryPoint.ParryThresholds

/-!
# Analytic enclosure of the Eulerian–Parry parameter

This file attempts the exact bridge from the real hyperbolic-sine value
to its twelve-place rational bracket, using Mathlib's rigorous
exponential Taylor remainder bound, without numerical axioms.
Only declarations accepted by the kernel and axiom audit are certified.
-/

namespace Manuscript14Section11

open scoped Topology

noncomputable def eulerianParryValue : ℝ :=
  Real.sqrt 2 * Real.sinh (1 / Real.sqrt 2)

/-- The actual real hyperbolic-sine special value lies in the exact
rational interval used in the Parry threshold and defect certificates. -/
theorem eulerianParryValue_rational_bracket :
    (1085441641272 : ℝ) / 10 ^ 12 < eulerianParryValue ∧
      eulerianParryValue < (1085441641273 : ℝ) / 10 ^ 12 := by
  let q : ℝ := Real.sqrt 2
  let u : ℝ := q / 2
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hq2 : q ^ 2 = 2 := by
    dsimp [q]
    norm_num
  have hqle : q ≤ 2 := by
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
  have hu2 : u ^ 2 = (1 / 2 : ℝ) := by
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

  let s7 : ℝ := (16516703560751 : ℝ) / 15216574464000
  have hpow (k : ℕ) : q * u ^ (2 * k + 1) = (1 / 2 : ℝ) ^ k := by
    calc
      q * u ^ (2 * k + 1) = (q * u) * (u ^ 2) ^ k := by
        rw [show 2 * k + 1 = 1 + 2 * k by omega, pow_add, pow_mul]
        ring
      _ = (1 / 2 : ℝ) ^ k := by rw [hqu, hu2, one_mul]
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
      |eulerianParryValue - s7| ≤ q * E := by
    have heq : eulerianParryValue - s7 =
        (q / 2) * ((Real.exp u - Real.exp (-u)) - (Splus - Sminus)) := by
      dsimp [eulerianParryValue]
      change q * Real.sinh (1 / q) - s7 = _
      rw [huinv, Real.sinh_eq, ← hseven]
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < q / 2)]
    calc
      (q / 2) * |(Real.exp u - Real.exp (-u)) - (Splus - Sminus)| ≤
          (q / 2) * (2 * E) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = q * E := by ring
  have hqerr : q * E ≤ 2 * E :=
    mul_le_mul_of_nonneg_right hqle hEnonneg
  have hnumlo :
      (1085441641272 : ℝ) / 10 ^ 12 + 2 * E < s7 := by
    norm_num [s7, E, Nat.factorial]
  have hnumhi :
      s7 + 2 * E < (1085441641273 : ℝ) / 10 ^ 12 := by
    norm_num [s7, E, Nat.factorial]
  obtain ⟨hl, hh⟩ := abs_le.mp hxe
  constructor <;> dsimp [eulerianParryValue] at * <;> linarith

#print axioms Manuscript14Section11.eulerianParryValue_rational_bracket

/-!
## Removing the analytic-bracket hypothesis from the genuine floor dynamics

This is the complete kernel-checked *dynamical and numerical part*
of the manuscript's sole Section 11 theorem.  The transcendence and
non-eventual-periodicity assertions remain distinct obligations.
-/

/-- No interval hypothesis: the actual Eulerian hyperbolic value satisfies
the digit prefix, adjacent-root straddling, exact critical-orbit defect
and the simple-Parry endpoint jump. -/
theorem eulerian_parry_dynamical_part_unconditional :
    (greedyDigit eulerianParameter 0 = 1 ∧
      (∀ k : ℕ, k < 30 → greedyDigit eulerianParameter (k + 1) = 0) ∧
      greedyDigit eulerianParameter 31 = 1) ∧
    ((313240 : ℝ) / 10 ^ 9 <
      1 - (greedyMap eulerianParameter)^[31] 1 ∧
      1 - (greedyMap eulerianParameter)^[31] 1 <
        (313241 : ℝ) / 10 ^ 9) ∧
    (∃ beta32 beta31 : ℝ,
      (1 < beta32 ∧ beta32 < 2 ∧ beta32 ^ 32 - beta32 ^ 31 - 1 = 0) ∧
      (1 < beta31 ∧ beta31 < 2 ∧ beta31 ^ 31 - beta31 ^ 30 - 1 = 0) ∧
      beta32 < eulerianParameter ∧ eulerianParameter < beta31 ∧
      (greedyMap beta31)^[31] 1 = 0 ∧
      Filter.Tendsto (fun beta : ℝ => (greedyMap beta)^[31] 1)
        (𝓝[<] beta31) (𝓝 (1 : ℝ))) := by
  have hbracket :
      (1085441641272 : ℝ) / 10 ^ 12 < eulerianParameter ∧
      eulerianParameter < (1085441641273 : ℝ) / 10 ^ 12 := by
    simpa [eulerianParameter, eulerianParryValue] using
      eulerianParryValue_rational_bracket
  exact eulerian_parry_theorem_conditional hbracket.1 hbracket.2

#print axioms Manuscript14Section11.eulerian_parry_dynamical_part_unconditional


end Manuscript14Section11
