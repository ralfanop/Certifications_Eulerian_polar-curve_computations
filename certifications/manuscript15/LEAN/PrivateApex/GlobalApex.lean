import PrivateApex.OddSlopeTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
PRIVATE: Manuscript 15, Theorem 7.3 -- global minimum of the virtual apex angle.

`slopeQ n` is the exact central slope of the Eulerian profile of order `n`
(`s_n` for odd `n`, `t_n` for even `n`; see `slopeQ_odd`, `slopeQ_even`).
The 34 even and 35 odd finite comparisons of `FiniteComparisons` are combined with the
infinite tails of `OddSlopeTail` (`s_n < 1` for odd `n ≥ 73`, `t_n < 2` for even `n ≥ 72`).
No uniform bound is assumed: every tail estimate is derived from the Eulerian numbers `E`
through the Fourier integral of `EulerianCert.EulerianFourier`.

Main statements, for every integer `n ≥ 3`:
* `slopeQ_classification`: `0 < slopeQ n ≤ 9473633/3628800`, with equality iff `n = 12`;
  `2 < slopeQ n` iff `n` is even and `n ≤ 48`; `slopeQ n = 2` iff `n = 3` or `n = 5`;
* `virtualApex_unique_min`: `α₁₂^virt < α_n^virt` for `n ≠ 12`, where
  `α_n^virt = 2 arctan(1/slopeQ n) = 2 arccot(slopeQ n)`;
* `virtualApex_twelve`: `α₁₂^virt = 2 arctan(3628800/9473633) = 2 arccot(9473633/3628800)`;
* `virtualApex_threshold`: the comparison with `α₃ = 2 arctan(1/2)`.
-/
noncomputable section
namespace PrivateApex
open Real

/-- The maximal slope `t₁₂ = 9473633/3628800`. -/
def peak : ℚ := 9473633 / 3628800

theorem two_lt_peak : (2 : ℚ) < peak := by unfold peak; norm_num

theorem even_small {m : ℕ} (h2 : 2 ≤ m) (h35 : m ≤ 35) :
    0 < slopeQ (2 * m) ∧ (slopeQ (2 * m) = 9473633 / 3628800 ↔ 2 * m = 12) ∧
    slopeQ (2 * m) ≤ 9473633 / 3628800 ∧ (2 < slopeQ (2 * m) ↔ 2 * m ≤ 48) ∧
    (50 ≤ 2 * m → slopeQ (2 * m) < 2) := by
  have h : 0 < slopeQ (2 * (m - 2 + 2)) ∧
      (slopeQ (2 * (m - 2 + 2)) = 9473633 / 3628800 ↔ 2 * (m - 2 + 2) = 12) ∧
      slopeQ (2 * (m - 2 + 2)) ≤ 9473633 / 3628800 ∧
      (2 < slopeQ (2 * (m - 2 + 2)) ↔ 2 * (m - 2 + 2) ≤ 48) ∧
      (50 ≤ 2 * (m - 2 + 2) → slopeQ (2 * (m - 2 + 2)) < 2) :=
    finite_even_rationals ⟨m - 2, by omega⟩
  rwa [show m - 2 + 2 = m by omega] at h

theorem odd_small {j : ℕ} (h1 : 1 ≤ j) (h35 : j ≤ 35) :
    0 < slopeQ (2 * j + 1) ∧ slopeQ (2 * j + 1) ≤ 2 ∧
    (slopeQ (2 * j + 1) = 2 ↔ 2 * j + 1 = 3 ∨ 2 * j + 1 = 5) := by
  have h : 0 < slopeQ (2 * (j - 1) + 3) ∧ slopeQ (2 * (j - 1) + 3) ≤ 2 ∧
      (slopeQ (2 * (j - 1) + 3) = 2 ↔ 2 * (j - 1) + 3 = 3 ∨ 2 * (j - 1) + 3 = 5) :=
    finite_odd_rationals ⟨j - 1, by omega⟩
  rwa [show 2 * (j - 1) + 3 = 2 * j + 1 by omega] at h

/-- **Classification of all central slopes** (Theorem 7.3, slope form). -/
theorem slopeQ_classification (n : ℕ) (hn : 3 ≤ n) :
    0 < slopeQ n ∧ slopeQ n ≤ peak ∧ (slopeQ n = peak ↔ n = 12) ∧
    (2 < slopeQ n ↔ Even n ∧ n ≤ 48) ∧ (slopeQ n = 2 ↔ n = 3 ∨ n = 5) := by
  have hp := two_lt_peak
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- even order `n = 2m ≥ 4`
    have hev : Even (2 * m) := even_two_mul m
    by_cases hm : m ≤ 35
    · obtain ⟨h0, h1, h2, h3, h4⟩ := even_small (by omega) hm
      refine ⟨h0, h2, h1, ?_, ?_⟩
      · rw [h3]; exact ⟨fun h => ⟨hev, h⟩, fun h => h.2⟩
      · constructor
        · intro h
          by_cases h48 : 2 * m ≤ 48
          · have := h3.mpr h48; linarith
          · have := h4 (by omega); linarith
        · intro h; omega
    · obtain ⟨h0, h2⟩ := slopeQ_even_tail (m := m) (by omega)
      refine ⟨h0, by linarith, ?_, ?_, ?_⟩
      · constructor
        · intro h; linarith
        · intro h; omega
      · constructor
        · intro h; linarith
        · intro h; omega
      · constructor
        · intro h; linarith
        · intro h; omega
  · -- odd order `n = 2m+1 ≥ 3`
    have hodd : ¬ Even (2 * m + 1) := by
      rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one m
    by_cases hm : m ≤ 35
    · obtain ⟨h0, h1, h2⟩ := odd_small (by omega) hm
      refine ⟨h0, by linarith, ?_, ?_, h2⟩
      · constructor
        · intro h; linarith
        · intro h; omega
      · constructor
        · intro h; linarith
        · intro h; exact absurd h.1 hodd
    · have h0 := slopeQ_odd_pos (j := m) (by omega)
      have h1 := slopeQ_odd_lt_one (j := m) (by omega)
      refine ⟨h0, by linarith, ?_, ?_, ?_⟩
      · constructor
        · intro h; linarith
        · intro h; omega
      · constructor
        · intro h; linarith
        · intro h; exact absurd h.1 hodd
      · constructor
        · intro h; linarith
        · intro h; omega

theorem slopeQ_twelve : slopeQ 12 = peak := (slopeQ_classification 12 (by norm_num)).2.2.1.mpr rfl

/-- **Uniqueness of the maximal slope**: `slopeQ n < slopeQ 12` for every `n ≥ 3`, `n ≠ 12`. -/
theorem slopeQ_lt_twelve (n : ℕ) (hn : 3 ≤ n) (h12 : n ≠ 12) : slopeQ n < slopeQ 12 := by
  obtain ⟨_, hle, heq, _, _⟩ := slopeQ_classification n hn
  rw [slopeQ_twelve]
  exact lt_of_le_of_ne hle (fun h => h12 (heq.mp h))

/-- The tail statement of Theorem 7.3: `t_n < 2` for every even `n ≥ 50`, and `s_n < 2` for
every odd `n ≥ 7`. -/
theorem slopeQ_lt_two (n : ℕ) (hn : 3 ≤ n) (h : (Even n ∧ 50 ≤ n) ∨ (¬ Even n ∧ 7 ≤ n)) :
    slopeQ n < 2 := by
  obtain ⟨_, _, _, hgt, heq⟩ := slopeQ_classification n hn
  have h1 : ¬ 2 < slopeQ n := by
    rw [hgt]; rcases h with h | h
    · intro h'; omega
    · intro h'; exact h.1 h'.1
  have h2 : slopeQ n ≠ 2 := by
    rw [Ne, heq]; rcases h with h | h <;> omega
  exact lt_of_le_of_ne (not_lt.mp h1) h2

/-! ### Angles -/

/-- The virtual apex angle `α_n^virt = 2 arccot(slopeQ n)`, written `2 arctan(1/slopeQ n)`
(the two agree because `slopeQ n > 0` for `n ≥ 3`).  For odd `n` it is the interior apex
angle `α_n`; for even `n` it is the angle between the two extended shoulders of the plateau. -/
def virtualApex (n : ℕ) : ℝ := 2 * arctan (1 / ((slopeQ n : ℚ) : ℝ))

/-- `α_n^virt = π - 2 arctan(slopeQ n)` for `n ≥ 3`. -/
theorem virtualApex_eq (n : ℕ) (hn : 3 ≤ n) :
    virtualApex n = π - 2 * arctan ((slopeQ n : ℚ) : ℝ) := by
  have h0 : (0 : ℝ) < ((slopeQ n : ℚ) : ℝ) := by
    exact_mod_cast (slopeQ_classification n hn).1
  unfold virtualApex
  rw [one_div, arctan_inv_of_pos h0]
  ring

/-- Strict anti-monotonicity of `t ↦ 2 arctan(1/t)` on positive rationals. -/
theorem angle_lt_of_slope_lt {a b : ℚ} (ha : 0 < a) (hab : a < b) :
    2 * arctan (1 / ((b : ℚ) : ℝ)) < 2 * arctan (1 / ((a : ℚ) : ℝ)) := by
  have ha' : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have : 1 / (b : ℝ) < 1 / (a : ℝ) := one_div_lt_one_div_of_lt ha' hab'
  linarith [arctan_strictMono this]

/-- **Theorem 7.3, uniqueness of the global minimum**: for every order `n ≥ 3` other than `12`,
`α₁₂^virt < α_n^virt`. -/
theorem virtualApex_unique_min (n : ℕ) (hn : 3 ≤ n) (h12 : n ≠ 12) :
    virtualApex 12 < virtualApex n :=
  angle_lt_of_slope_lt (slopeQ_classification n hn).1 (slopeQ_lt_twelve n hn h12)

/-- **Theorem 7.3, value of the minimum**: `α₁₂^virt = 2 arctan(3628800/9473633)`,
that is `2 arccot(9473633/3628800)`. -/
theorem virtualApex_twelve : virtualApex 12 = 2 * arctan (3628800 / 9473633) := by
  unfold virtualApex
  rw [slopeQ_twelve]
  unfold peak
  congr 2
  push_cast
  norm_num

/-- `α₁₂^virt ≤ α_n^virt` for every `n ≥ 3`: the minimum is attained at `n = 12`. -/
theorem virtualApex_min (n : ℕ) (hn : 3 ≤ n) : virtualApex 12 ≤ virtualApex n := by
  by_cases h : n = 12
  · subst h; exact le_rfl
  · exact (virtualApex_unique_min n hn h).le

/-- **Theorem 7.3, exact threshold** relative to `α₃ = α₅ = 2 arctan(1/2)`:
`α_n^virt < α₃` iff `n` is even and `n ≤ 48`; `α_n^virt = α₃` iff `n ∈ {3, 5}`;
`α_n^virt > α₃` otherwise. -/
theorem virtualApex_threshold (n : ℕ) (hn : 3 ≤ n) :
    (virtualApex n < 2 * arctan (1 / 2) ↔ Even n ∧ n ≤ 48) ∧
    (virtualApex n = 2 * arctan (1 / 2) ↔ n = 3 ∨ n = 5) ∧
    (2 * arctan (1 / 2) < virtualApex n ↔ ¬ (Even n ∧ n ≤ 48) ∧ ¬ (n = 3 ∨ n = 5)) := by
  obtain ⟨h0, _, _, hgt, heq⟩ := slopeQ_classification n hn
  have h0' : (0 : ℝ) < ((slopeQ n : ℚ) : ℝ) := by exact_mod_cast h0
  have key : ∀ x : ℝ, 0 < x →
      ((2 * arctan (1 / x) < 2 * arctan (1 / 2) ↔ 2 < x) ∧
       (2 * arctan (1 / x) = 2 * arctan (1 / 2) ↔ x = 2) ∧
       (2 * arctan (1 / 2) < 2 * arctan (1 / x) ↔ x < 2)) := by
    intro x hx
    have e1 : 1 / x < 1 / 2 ↔ 2 < x := one_div_lt_one_div hx (by norm_num)
    have e2 : 1 / 2 < 1 / x ↔ x < 2 := one_div_lt_one_div (by norm_num) hx
    refine ⟨?_, ?_, ?_⟩
    · rw [← e1, ← arctan_lt_arctan_iff (x := 1 / x) (y := 1 / 2)]
      constructor <;> intro h <;> linarith
    · constructor
      · intro h
        have h' : arctan (1 / x) = arctan (1 / 2) := by linarith
        have := arctan_injective h'
        field_simp at this
        linarith
      · intro h; rw [h]
    · rw [← e2, ← arctan_lt_arctan_iff (x := 1 / 2) (y := 1 / x)]
      constructor <;> intro h <;> linarith
  obtain ⟨k1, k2, k3⟩ := key _ h0'
  have c1 : (2 : ℝ) < ((slopeQ n : ℚ) : ℝ) ↔ 2 < slopeQ n := by exact_mod_cast Iff.rfl
  have c2 : ((slopeQ n : ℚ) : ℝ) = 2 ↔ slopeQ n = 2 := by exact_mod_cast Iff.rfl
  have c3 : ((slopeQ n : ℚ) : ℝ) < 2 ↔ slopeQ n < 2 := by exact_mod_cast Iff.rfl
  unfold virtualApex
  refine ⟨by rw [k1, c1, hgt], by rw [k2, c2, heq], ?_⟩
  rw [k3, c3, ← hgt, ← heq]
  constructor
  · intro h; exact ⟨by linarith, by intro h'; linarith⟩
  · intro h; exact lt_of_le_of_ne (not_lt.mp h.1) h.2

/-- Exactly 23 even orders (`n = 4, 6, …, 48`) have a virtual apex angle below `α₃`. -/
theorem card_even_below :
    ((Finset.Icc 3 200).filter (fun n => Even n ∧ n ≤ 48)).card = 23 := by decide

#print axioms slopeQ_classification
#print axioms slopeQ_lt_twelve
#print axioms slopeQ_lt_two
#print axioms virtualApex_eq
#print axioms virtualApex_unique_min
#print axioms virtualApex_twelve
#print axioms virtualApex_min
#print axioms virtualApex_threshold
end PrivateApex
