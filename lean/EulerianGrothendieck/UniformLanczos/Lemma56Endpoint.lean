import UniformLanczos.Lemma56
import UniformLanczos.Profile
import Bridge.Saddle.RightTail

/-!
# Manuscript 12, Lemma 5.6 (endpoint part) and Lemma 5.7(a) for the actual `φ_M`

Source: frozen `12.tex`, labels `lem:ul-spline` and `lem:ul-endpoint`.

From the exact density of `w_M` on its last knot interval (`Bridge.Saddle.RightTail`) and the
derivative formula `(w (M+1))' = w M (· + 1/2) - w M (· - 1/2)` (`Bridge.Saddle.LogConcave`):

* `w_logDeriv_tail`: `w_M'/w_M = -(M-1)/δ` at `y = M/2 - δ`, `0 < δ < 1`;
* `deriv_φM_tail`: `φ_M'(x) = (M-1)/(M(1/2-x))` on the last knot interval, `M ≥ 3`;
* `lemma_5_6_blowup`: `x φ_M'(x) ≥ c_M/(1/2-x)` for `1/2 - 1/(2M) ≤ x < 1/2`, with
  `c_M = (1/2 - 1/(2M))(M-1)/M > 0` (last sentence of Lemma 5.6, `M ≥ 3`);
* `lemma_5_6_G_strictMono`: `y ↦ y φ_M'(y)` is strictly increasing on `[0, 1/2)`;
* `lemma_5_7a_actual`: **Lemma 5.7(a)** for the actual `φ_M`, `M ≥ 3`: the equation
  `Φ_M(ξ) = t` has a unique root in `(0, 1/2)` for every `t > 0`.  No hypothesis remains.

The cases `M = 2` and `M = 1` of Lemma 5.6 are not in this file.
-/

open Set Filter Topology
open EulerianBridge.Saddle

namespace UniformLanczos.Lemma56

/-- On the last knot interval `w_M'/w_M = -(M-1)/δ` at `y = M/2 - δ`, here with `M = m + 2`. -/
theorem w_logDeriv_tail (m : ℕ) (hm : 1 ≤ m) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    deriv (w (m + 1 + 1)) (((m + 1 + 1 : ℕ) : ℝ) / 2 - δ) /
      w (m + 1 + 1) (((m + 1 + 1 : ℕ) : ℝ) / 2 - δ) = -((m:ℝ) + 1) / δ := by
  have hd := (hasDerivAt_w_succ (m + 1) (by omega) (((m + 1 + 1 : ℕ) : ℝ) / 2 - δ)).deriv
  have e1 : ((m + 1 + 1 : ℕ) : ℝ) / 2 - δ - 1/2 = ((m + 1 : ℕ) : ℝ) / 2 - δ := by
    push_cast
    ring
  have hz : w (m + 1) (((m + 1 + 1 : ℕ) : ℝ) / 2 - δ + 1/2) = 0 := by
    apply w_support (m + 1) (by omega)
    rw [lt_abs]
    left
    push_cast
    linarith
  have h1 := w_right_tail m δ hδ0.le hδ1
  have h2 := w_right_tail (m + 1) δ hδ0.le hδ1
  rw [hd, hz, e1, h1, h2, Nat.factorial_succ]
  have hf : ((m.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have hδ : δ ≠ 0 := hδ0.ne'
  have hm1 : (m:ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  try ring

/-- **Lemma 5.6**, endpoint formula: `φ_M'(x) = (M-1)/(M(1/2-x))` on the last knot interval. -/
theorem deriv_φM_tail {M : ℕ} (hM : 3 ≤ M) {x : ℝ} (hx0 : 0 < (M:ℝ) * (1/2 - x))
    (hx1 : (M:ℝ) * (1/2 - x) < 1) :
    deriv (φM M) x = ((M:ℝ) - 1) / ((M:ℝ) * (1/2 - x)) := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 + 1 := ⟨M - 2, by omega⟩
  have hm : 1 ≤ m := by omega
  have hM3 : (3:ℝ) ≤ ((m + 1 + 1 : ℕ) : ℝ) := by exact_mod_cast hM
  have hMpos : (0:ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by linarith
  have hxI : x ∈ Ioo (-(1/2):ℝ) (1/2) := by
    constructor
    · by_contra hneg
      push_neg at hneg
      nlinarith [mul_le_mul_of_nonneg_left (show (1:ℝ) ≤ 1/2 - x by linarith) hMpos.le]
    · by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg hMpos.le (show (0:ℝ) ≤ x - 1/2 by linarith)]
  have hpos := w_scaled_pos (M := m + 1 + 1) (by omega) hxI
  have harg : ((m + 1 + 1 : ℕ) : ℝ) * x =
      ((m + 1 + 1 : ℕ) : ℝ) / 2 - ((m + 1 + 1 : ℕ) : ℝ) * (1/2 - x) := by ring
  rw [(hasDerivAt_φM_three hM hpos).deriv, harg, w_logDeriv_tail m hm hx0 hx1]
  push_cast
  ring

/-- `y ↦ y φ_M'(y)` is strictly increasing on `[0, 1/2)`, `M ≥ 3`. -/
theorem lemma_5_6_G_strictMono {M : ℕ} (hM : 3 ≤ M) :
    StrictMonoOn (fun y => y * deriv (φM M) y) (Ico 0 (1 / 2)) := by
  intro x hx y hy hxy
  have hmono := lemma_5_6_hm hM
  have hzero : deriv (φM M) 0 = 0 := deriv_φM_zero (by omega)
  have m0 : (0:ℝ) ∈ Ico (0:ℝ) (1 / 2) := ⟨le_rfl, by norm_num⟩
  have hxy' : deriv (φM M) x < deriv (φM M) y := hmono hx hy hxy
  have hy0 : deriv (φM M) 0 < deriv (φM M) y := hmono m0 hy (lt_of_le_of_lt hx.1 hxy)
  have hA : x * deriv (φM M) x ≤ x * deriv (φM M) y :=
    mul_le_mul_of_nonneg_left hxy'.le hx.1
  have hB : x * deriv (φM M) y < y * deriv (φM M) y :=
    mul_lt_mul_of_pos_right hxy (by linarith)
  show x * deriv (φM M) x < y * deriv (φM M) y
  linarith

/-- **Lemma 5.6**, last sentence, `M ≥ 3`: `x φ_M'(x) ≥ c_M / (1/2 - x)` near `1/2`. -/
theorem lemma_5_6_blowup {M : ℕ} (hM : 3 ≤ M) :
    ∀ x ∈ Ico (1 / 2 - 1 / (2 * (M:ℝ))) (1 / 2),
      ((1 / 2 - 1 / (2 * (M:ℝ))) * (((M:ℝ) - 1) / M)) / (1 / 2 - x) ≤ x * deriv (φM M) x := by
  intro x hx
  have hM3 : (3:ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0:ℝ) < M := by linarith
  have hMne : (M:ℝ) ≠ 0 := hMpos.ne'
  have hd : 0 < 1 / 2 - x := by linarith [hx.2]
  have hdne : 1 / 2 - x ≠ 0 := hd.ne'
  have hx0 : 0 < (M:ℝ) * (1 / 2 - x) := mul_pos hMpos hd
  have hx1 : (M:ℝ) * (1 / 2 - x) < 1 := by
    have h1 : 1 / 2 - x ≤ 1 / (2 * (M:ℝ)) := by linarith [hx.1]
    have h2 : (M:ℝ) * (1 / (2 * (M:ℝ))) = 1 / 2 := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 hMpos.le
    linarith
  rw [deriv_φM_tail hM hx0 hx1, div_le_iff₀ hd]
  have hk : x * (((M:ℝ) - 1) / ((M:ℝ) * (1 / 2 - x))) * (1 / 2 - x) =
      x * (((M:ℝ) - 1) / M) := by
    rw [mul_assoc, div_mul_eq_mul_div, mul_div_mul_right _ _ hdne]
  rw [hk]
  exact mul_le_mul_of_nonneg_right hx.1 (div_nonneg (by linarith) hMpos.le)

/-- **Lemma 5.7(a)** for the actual `φ_M`, `M ≥ 3`: `Φ_M(ξ) = t` has a unique root in
`(0, 1/2)` for every `t > 0`.  Here `Φ_M = Hint (fun y => y * φ_M'(y))`. -/
theorem lemma_5_7a_actual {M : ℕ} (hM : 3 ≤ M) {t : ℝ} (ht : 0 < t) :
    ∃ ξ ∈ Ioo (0:ℝ) (1 / 2), Hint (fun y => y * deriv (φM M) y) ξ = t ∧
      ∀ ξ' ∈ Ico (0:ℝ) (1 / 2), Hint (fun y => y * deriv (φM M) y) ξ' = t → ξ' = ξ := by
  have hM3 : (3:ℝ) ≤ M := by exact_mod_cast hM
  have hMpos : (0:ℝ) < M := by linarith
  have h6 : 1 / (2 * (M:ℝ)) ≤ 1 / 6 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hpos6 : 0 < 1 / (2 * (M:ℝ)) := by positivity
  have hx0 : (0:ℝ) ≤ 1 / 2 - 1 / (2 * (M:ℝ)) := by linarith
  have hx01 : 1 / 2 - 1 / (2 * (M:ℝ)) < 1 / 2 := by linarith
  have hc0 : 0 < (1 / 2 - 1 / (2 * (M:ℝ))) * (((M:ℝ) - 1) / M) :=
    mul_pos (by linarith) (div_pos (by linarith) hMpos)
  exact UniformLanczos.Profile.lemma_5_7a (fun y => y * deriv (φM M) y)
    (fun b hb => continuousOn_id.mul (lemma_5_6_hc hM b hb)) (lemma_5_6_G_strictMono hM)
    (by simp) hc0 hx0 hx01 (lemma_5_6_blowup hM) ht

end UniformLanczos.Lemma56

#print axioms UniformLanczos.Lemma56.w_logDeriv_tail
#print axioms UniformLanczos.Lemma56.deriv_φM_tail
#print axioms UniformLanczos.Lemma56.lemma_5_6_G_strictMono
#print axioms UniformLanczos.Lemma56.lemma_5_6_blowup
#print axioms UniformLanczos.Lemma56.lemma_5_7a_actual
