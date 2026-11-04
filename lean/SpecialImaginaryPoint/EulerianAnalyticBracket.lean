import Mathlib

/-!
# Analytic enclosure of the Eulerian–Parry parameter

This file attempts the exact bridge from the real hyperbolic-sine value
to its twelve-place rational bracket, using Mathlib's rigorous
exponential Taylor remainder bound, without numerical axioms.
Only declarations accepted by the kernel and axiom audit are certified.
-/

namespace Manuscript14Section11

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
  let E : ℝ := (17 : ℝ) * (((16.factorial : ℝ) * 16)⁻¹)
  have hEnonneg : 0 ≤ E := by
    dsimp [E]
    positivity
  have hpowle : |u| ^ 16 ≤ (1 : ℝ) :=
    pow_le_one₀ (abs_nonneg _) huabs
  have herror : |u| ^ 16 *
      ((16 + 1 : ℕ) : ℝ) * (((16.factorial : ℝ) * 16)⁻¹) ≤ E := by
    dsimp [E]
    nlinarith [mul_le_mul_of_nonneg_right hpowle
      (show (0 : ℝ) ≤ (17 : ℝ) * (((16.factorial : ℝ) * 16)⁻¹) by positivity)]
  have hplus : |Real.exp u - Splus| ≤ E := by
    have h := Real.exp_bound (x := u) huabs (n := 16) (by norm_num)
    have h' : |Real.exp u - Splus| ≤
        |u| ^ 16 * ((16 + 1 : ℕ) : ℝ) *
          (((16.factorial : ℝ) * 16)⁻¹) := by
      simpa only [Splus] using h
    exact h'.trans herror
  have hminus : |Real.exp (-u) - Sminus| ≤ E := by
    have h := Real.exp_bound (x := -u) hunegabs (n := 16) (by norm_num)
    have h' : |Real.exp (-u) - Sminus| ≤
        |u| ^ 16 * ((16 + 1 : ℕ) : ℝ) *
          (((16.factorial : ℝ) * 16)⁻¹) := by
      simpa only [Sminus, abs_neg] using h
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

end Manuscript14Section11
