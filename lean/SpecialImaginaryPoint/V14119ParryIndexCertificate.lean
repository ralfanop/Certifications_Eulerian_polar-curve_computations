import Mathlib

/-!
# Manuscript 14, version 14.119 (9 November 2026): the Parry index of the Eulerian values

Kernel-checked statements behind Proposition 10.2 and its display (176). For `β > 1` put
`quot β = log (1/(β - 1)) / log β`, the quotient of (176) with `β = sinh(x)/x`, and
`F_m(t) = t^(m-1)(t - 1) - 1`, written below through `t ^ m * (t - 1)` with `m` in place of `m - 1`.
The Arb values of `sinh(x)/x`, the asymptotics (177) and the greedy words for `x = k/100` are certified in
`numerics/arb/manuscript14_v14119_parry_index_arb.py`.

* `strictMonoOn_F`: `t ↦ t^m (t - 1)` is strictly increasing on `[1, ∞)`;
* `lt_root_iff`: if `r > 1` is a zero of `F_(m+1)`, then `β < r ↔ β^m (β - 1) < 1` for `β > 1`;
* `pow_mul_lt_one_iff`: `β^m (β - 1) < 1 ↔ m < quot β`;
* `pow_mul_eq_one_iff`: `β^m (β - 1) = 1 ↔ m = quot β`, so the quotient is an integer only at a root;
* `index_ceil`: `β^m (β - 1) < 1 < β^(m+1) (β - 1)` gives `⌈quot β⌉ = m + 1`, display (176);
* `remainders`, `greedy_word`: for `1 < β < 2` the greedy remainders of `1` are `β^j (β - 1)`,
  `0 ≤ j ≤ m`, and the greedy digits begin with `1 0^m 1`, that is `1 0^(n-1) 1` with `n = m + 1`;
* `index_b`, `index_a`: every `β` in the rational brackets of the proofs of Theorem 10.1 and of
  Proposition 10.2 has `⌈quot β⌉ = 31` and `⌈quot β⌉ = 187`;
* `margins_a`: the margins `F_187 < -1/200` and `F_188 > 1/100` of the proof of Proposition 10.2.
-/

namespace SpecialImaginaryPoint.V14119ParryIndex

/-- The quotient of (176), `log (1/(β - 1)) / log β`. -/
noncomputable def quot (β : ℝ) : ℝ := Real.log (1 / (β - 1)) / Real.log β

/-- The greedy map `T_β(y) = β y - ⌊β y⌋`. -/
noncomputable def T (β y : ℝ) : ℝ := β * y - ⌊β * y⌋

/-- The greedy digit `⌊β y⌋` produced at the remainder `y`. -/
noncomputable def digit (β y : ℝ) : ℤ := ⌊β * y⌋

theorem strictMonoOn_F (m : ℕ) : StrictMonoOn (fun t : ℝ => t ^ m * (t - 1)) (Set.Ici 1) := by
  intro s hs t ht hst
  simp only [Set.mem_Ici] at hs ht
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have h1 : s ^ m ≤ t ^ m := pow_le_pow_left₀ hs0 hst.le m
  have h2 : 0 < t ^ m := pow_pos (by linarith) m
  calc s ^ m * (s - 1) ≤ t ^ m * (s - 1) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ < t ^ m * (t - 1) := mul_lt_mul_of_pos_left (by linarith) h2

theorem lt_root_iff {β r : ℝ} (hβ : 1 < β) (hr : 1 < r) (m : ℕ) (hroot : r ^ m * (r - 1) = 1) :
    β < r ↔ β ^ m * (β - 1) < 1 := by
  have key : β ^ m * (β - 1) < r ^ m * (r - 1) ↔ β < r :=
    (strictMonoOn_F m).lt_iff_lt (Set.mem_Ici.mpr hβ.le) (Set.mem_Ici.mpr hr.le)
  rw [hroot] at key
  exact key.symm

theorem pow_mul_lt_one_iff {β : ℝ} (hβ : 1 < β) (m : ℕ) :
    β ^ m * (β - 1) < 1 ↔ (m : ℝ) < quot β := by
  have h0 : 0 < β - 1 := by linarith
  have hb : 0 < β := by linarith
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hpos : 0 < β ^ m * (β - 1) := mul_pos (pow_pos hb m) h0
  have hl : Real.log (β ^ m * (β - 1)) = (m : ℝ) * Real.log β + Real.log (β - 1) := by
    rw [Real.log_mul (pow_pos hb m).ne' h0.ne', Real.log_pow]
  have hq : Real.log (1 / (β - 1)) = -Real.log (β - 1) := by
    rw [one_div, Real.log_inv]
  unfold quot
  rw [lt_div_iff₀ hlog, hq, ← Real.log_lt_log_iff hpos one_pos, hl, Real.log_one]
  constructor <;> intro h <;> linarith

theorem pow_mul_eq_one_iff {β : ℝ} (hβ : 1 < β) (m : ℕ) :
    β ^ m * (β - 1) = 1 ↔ (m : ℝ) = quot β := by
  have h0 : 0 < β - 1 := by linarith
  have hb : 0 < β := by linarith
  have hlog : 0 < Real.log β := Real.log_pos hβ
  have hpos : 0 < β ^ m * (β - 1) := mul_pos (pow_pos hb m) h0
  have hl : Real.log (β ^ m * (β - 1)) = (m : ℝ) * Real.log β + Real.log (β - 1) := by
    rw [Real.log_mul (pow_pos hb m).ne' h0.ne', Real.log_pow]
  have hq : Real.log (1 / (β - 1)) = -Real.log (β - 1) := by
    rw [one_div, Real.log_inv]
  unfold quot
  rw [eq_div_iff hlog.ne', hq]
  constructor
  · intro h
    have h' := congrArg Real.log h
    rw [hl, Real.log_one] at h'
    linarith
  · intro h
    have h' : Real.log (β ^ m * (β - 1)) = 0 := by
      rw [hl]
      linarith
    exact Real.eq_one_of_pos_of_log_eq_zero hpos h'

theorem index_ceil {β : ℝ} (hβ : 1 < β) (m : ℕ)
    (hlo : β ^ m * (β - 1) < 1) (hhi : 1 < β ^ (m + 1) * (β - 1)) :
    ⌈quot β⌉ = (m : ℤ) + 1 := by
  have h1 : (m : ℝ) < quot β := (pow_mul_lt_one_iff hβ m).1 hlo
  have h2 : quot β ≤ (m : ℝ) + 1 := by
    by_contra hc
    have hc' : ((m + 1 : ℕ) : ℝ) < quot β := by
      push_cast
      exact not_le.mp hc
    have := (pow_mul_lt_one_iff hβ (m + 1)).2 hc'
    linarith
  rw [Int.ceil_eq_iff]
  push_cast
  constructor
  · linarith
  · exact h2

theorem remainders {β : ℝ} (hβ : 1 < β) (hβ2 : β < 2) (m : ℕ)
    (hlo : β ^ m * (β - 1) < 1) :
    ∀ j ≤ m, (T β)^[j + 1] 1 = β ^ j * (β - 1) := by
  have h0 : 0 < β - 1 := by linarith
  intro j
  induction j with
  | zero =>
    intro _
    have hfl : ⌊β⌋ = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hβ.le
      · exact_mod_cast (show β < (1 : ℝ) + 1 by linarith)
    show T β 1 = β ^ 0 * (β - 1)
    simp only [T, mul_one, hfl, Int.cast_one, pow_zero, one_mul]
  | succ k ih =>
    intro hj
    have hk : k ≤ m := Nat.le_of_succ_le hj
    rw [Function.iterate_succ_apply', ih hk]
    have hpow : β ^ (k + 1) ≤ β ^ m := pow_le_pow_right₀ hβ.le hj
    have hle : β ^ (k + 1) * (β - 1) ≤ β ^ m * (β - 1) := mul_le_mul_of_nonneg_right hpow h0.le
    have heq : β * (β ^ k * (β - 1)) = β ^ (k + 1) * (β - 1) := by ring
    have hlt : β * (β ^ k * (β - 1)) < 1 := by
      rw [heq]
      exact lt_of_le_of_lt hle hlo
    have hnn : 0 ≤ β * (β ^ k * (β - 1)) :=
      mul_nonneg (by linarith) (mul_nonneg (pow_nonneg (by linarith) k) h0.le)
    have hfl : ⌊β * (β ^ k * (β - 1))⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast hnn
      · exact_mod_cast (show β * (β ^ k * (β - 1)) < (0 : ℝ) + 1 by linarith)
    simp only [T, hfl, Int.cast_zero, sub_zero]
    exact heq

theorem greedy_word {β : ℝ} (hβ : 1 < β) (hβ2 : β < 2) (m : ℕ)
    (hlo : β ^ m * (β - 1) < 1) (hhi : 1 < β ^ (m + 1) * (β - 1)) :
    digit β 1 = 1 ∧ (∀ j < m, digit β ((T β)^[j + 1] 1) = 0) ∧
      digit β ((T β)^[m + 1] 1) = 1 := by
  have h0 : 0 < β - 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold digit
    rw [mul_one, Int.floor_eq_iff]
    constructor
    · exact_mod_cast hβ.le
    · exact_mod_cast (show β < (1 : ℝ) + 1 by linarith)
  · intro j hj
    unfold digit
    rw [remainders hβ hβ2 m hlo j hj.le]
    have hpow : β ^ (j + 1) ≤ β ^ m := pow_le_pow_right₀ hβ.le (Nat.succ_le_of_lt hj)
    have hle : β ^ (j + 1) * (β - 1) ≤ β ^ m * (β - 1) := mul_le_mul_of_nonneg_right hpow h0.le
    have heq : β * (β ^ j * (β - 1)) = β ^ (j + 1) * (β - 1) := by ring
    have hnn : 0 ≤ β * (β ^ j * (β - 1)) :=
      mul_nonneg (by linarith) (mul_nonneg (pow_nonneg (by linarith) j) h0.le)
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast hnn
    · exact_mod_cast (show β * (β ^ j * (β - 1)) < (0 : ℝ) + 1 by rw [heq]; linarith)
  · unfold digit
    rw [remainders hβ hβ2 m hlo m le_rfl]
    have heq : β * (β ^ m * (β - 1)) = β ^ (m + 1) * (β - 1) := by ring
    have h3 : β * (β ^ m * (β - 1)) < β * 1 := mul_lt_mul_of_pos_left hlo (by linarith)
    rw [Int.floor_eq_iff]
    constructor
    · exact_mod_cast (show (1 : ℝ) ≤ β * (β ^ m * (β - 1)) by rw [heq]; exact hhi.le)
    · exact_mod_cast (show β * (β ^ m * (β - 1)) < (1 : ℝ) + 1 by linarith)

/-- The rational bracket `10854/10^4 < β_E < 1085445/10^6` of the proof of Theorem 10.1 gives the
index `31` of (176) at `x = 1/√2`. -/
theorem index_b {β : ℝ} (hlo : (10854 : ℝ) / 10 ^ 4 < β) (hhi : β < (1085445 : ℝ) / 10 ^ 6) :
    ⌈quot β⌉ = 31 := by
  have hl1 : (1 : ℝ) < 10854 / 10 ^ 4 := by norm_num
  have hh1 : (1 : ℝ) ≤ 1085445 / 10 ^ 6 := by norm_num
  have h1 : 1 < β := lt_trans hl1 hlo
  have e1 : ((1085445 : ℝ) / 10 ^ 6) ^ 30 * ((1085445 : ℝ) / 10 ^ 6 - 1) < 1 := by norm_num
  have e2 : (1 : ℝ) < ((10854 : ℝ) / 10 ^ 4) ^ 31 * ((10854 : ℝ) / 10 ^ 4 - 1) := by norm_num
  have k1 : β ^ 30 * (β - 1) < ((1085445 : ℝ) / 10 ^ 6) ^ 30 * ((1085445 : ℝ) / 10 ^ 6 - 1) :=
    ((strictMonoOn_F 30).lt_iff_lt (Set.mem_Ici.mpr h1.le) (Set.mem_Ici.mpr hh1)).2 hhi
  have k2 : ((10854 : ℝ) / 10 ^ 4) ^ 31 * ((10854 : ℝ) / 10 ^ 4 - 1) < β ^ 31 * (β - 1) :=
    ((strictMonoOn_F 31).lt_iff_lt (Set.mem_Ici.mpr hl1.le) (Set.mem_Ici.mpr h1.le)).2 hlo
  have := index_ceil h1 30 (lt_trans k1 e1) (lt_trans e2 k2)
  rw [this]
  norm_num

/-- The rational bracket `1020963929/10^9 < r_E(z_0) < 1020963930/10^9` of the proof of Proposition 10.2
gives the index `187` of (176) at `x = 1/√8`, through `F_187 < -1/200` and `F_188 > 1/100`. -/
theorem index_a {β : ℝ} (hlo : (1020963929 : ℝ) / 10 ^ 9 < β) (hhi : β < (1020963930 : ℝ) / 10 ^ 9) :
    ⌈quot β⌉ = 187 := by
  have hl1 : (1 : ℝ) < 1020963929 / 10 ^ 9 := by norm_num
  have hh1 : (1 : ℝ) ≤ 1020963930 / 10 ^ 9 := by norm_num
  have h1 : 1 < β := lt_trans hl1 hlo
  have e1 : ((1020963930 : ℝ) / 10 ^ 9) ^ 186 * ((1020963930 : ℝ) / 10 ^ 9 - 1) < 1 := by norm_num
  have e2 : (1 : ℝ) < ((1020963929 : ℝ) / 10 ^ 9) ^ 187 * ((1020963929 : ℝ) / 10 ^ 9 - 1) := by norm_num
  have k1 : β ^ 186 * (β - 1) <
      ((1020963930 : ℝ) / 10 ^ 9) ^ 186 * ((1020963930 : ℝ) / 10 ^ 9 - 1) :=
    ((strictMonoOn_F 186).lt_iff_lt (Set.mem_Ici.mpr h1.le) (Set.mem_Ici.mpr hh1)).2 hhi
  have k2 : ((1020963929 : ℝ) / 10 ^ 9) ^ 187 * ((1020963929 : ℝ) / 10 ^ 9 - 1) <
      β ^ 187 * (β - 1) :=
    ((strictMonoOn_F 187).lt_iff_lt (Set.mem_Ici.mpr hl1.le) (Set.mem_Ici.mpr h1.le)).2 hlo
  have := index_ceil h1 186 (lt_trans k1 e1) (lt_trans e2 k2)
  rw [this]
  norm_num

/-- The margins `F_187 < -1/200` at the right endpoint and `F_188 > 1/100` at the left endpoint of the
bracket of `r_E(z_0)` in the proof of Proposition 10.2, in exact rational arithmetic. -/
theorem margins_a :
    ((1020963930 : ℚ) / 10 ^ 9) ^ 186 * ((1020963930 : ℚ) / 10 ^ 9 - 1) - 1 < -1 / 200 ∧
      (1 : ℚ) / 100 < ((1020963929 : ℚ) / 10 ^ 9) ^ 187 * ((1020963929 : ℚ) / 10 ^ 9 - 1) - 1 := by
  constructor <;> norm_num

end SpecialImaginaryPoint.V14119ParryIndex

#print axioms SpecialImaginaryPoint.V14119ParryIndex.strictMonoOn_F
#print axioms SpecialImaginaryPoint.V14119ParryIndex.lt_root_iff
#print axioms SpecialImaginaryPoint.V14119ParryIndex.pow_mul_lt_one_iff
#print axioms SpecialImaginaryPoint.V14119ParryIndex.pow_mul_eq_one_iff
#print axioms SpecialImaginaryPoint.V14119ParryIndex.index_ceil
#print axioms SpecialImaginaryPoint.V14119ParryIndex.remainders
#print axioms SpecialImaginaryPoint.V14119ParryIndex.greedy_word
#print axioms SpecialImaginaryPoint.V14119ParryIndex.index_b
#print axioms SpecialImaginaryPoint.V14119ParryIndex.index_a
#print axioms SpecialImaginaryPoint.V14119ParryIndex.margins_a
