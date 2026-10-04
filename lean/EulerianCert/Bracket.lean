/-
# Remark 3.16 of the V478 manuscript (crossing order: central polygonal angles at n = 669, 671)

`E(n,k)`, `0 ≤ k ≤ n - 1`, denotes the Eulerian numbers in Deza's convention, as in §2 of the
manuscript (permutations of `{1, …, n}` with exactly `k` ascents): `E(1,0) = 1`,
`E(n+1,k) = (k+1) E(n,k) + (n+1-k) E(n,k-1)` for `k ≥ 1`, `E(n+1,0) = E(n,0)`, and
`E(n,k) = 0` for `k ≥ n`.

* `row`, `E`: the triangle computed row by row in one linear pass per row.  The definitions use
  the raw recursors `Nat.rec`/`List.rec`, so that the Lean kernel evaluates them with little
  overhead.
* `E_one_zero`, `E_eq_zero_of_le`, `E_succ_zero`, `E_succ`: the definition satisfies exactly the
  initial values and the recurrence above.  These facts determine `E` uniquely, so `E` is the
  Eulerian triangle of the manuscript.  The combinatorial meaning (permutations with `k` ascents)
  is classical and is not re-proved here.
* `c669_lt`, `c671_gt`: by evaluation in the Lean kernel (`decide +kernel`; no `native_decide`,
  hence no trust in the compiler), the integer inequalities equivalent to

    `c_669 < 333/106`   and   `355/113 < c_671`,
    `c_n = 1/s_n = n! / ((n+1) (E(n,(n-1)/2) - E(n,(n-3)/2)))`,

  since `p_{n,k} = E(n,k-1)/n!` (Eq. 76) and `s_n = (n+1)(p_{n,(n+1)/2} - p_{n,(n-1)/2})`.
* `angle_bracket`: with `333/106 < π < 355/113` (from Mathlib's bounds on `π`) and the strict
  monotonicity of `arctan`, `α_671 < ϑ_E < α_669`, where `α_n = 2 arccot c_n` and
  `ϑ_E = 2 arccot π`.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

namespace EulerianCert.Bracket

/-! ### The Eulerian triangle -/

/-- One pass of the recurrence.  For `r = [a₀, a₁, …, a_{L-1}]`,
`go m r prev k = [k a₀ + (m+2-k) prev, (k+1) a₁ + (m+1-k) a₀, …, (m+2-k-L) a_{L-1}]`. -/
noncomputable def go (m : ℕ) : List ℕ → ℕ → ℕ → List ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ → List ℕ) (fun prev k => [(m + 2 - k) * prev])
    (fun a _ ih prev k => (k * a + (m + 2 - k) * prev) :: ih a (k + 1))

@[simp] lemma go_nil (m prev k : ℕ) : go m [] prev k = [(m + 2 - k) * prev] := rfl

@[simp] lemma go_cons (m a : ℕ) (as : List ℕ) (prev k : ℕ) :
    go m (a :: as) prev k = (k * a + (m + 2 - k) * prev) :: go m as a (k + 1) := rfl

/-- `row n = [E(n,0), …, E(n,n-1)]`. -/
noncomputable def row (n : ℕ) : List ℕ :=
  @Nat.rec (fun _ => List ℕ) []
    (fun m r => @Nat.rec (fun _ => List ℕ) [1] (fun _ _ => go m r 0 1) m) n

lemma row_zero : row 0 = [] := rfl
lemma row_one : row 1 = [1] := rfl
lemma row_succ_succ (m : ℕ) : row (m + 2) = go (m + 1) (row (m + 1)) 0 1 := rfl

/-- `E n k` (`0 ≤ k ≤ n - 1`; `E n k = 0` for `k ≥ n`). -/
noncomputable def E (n k : ℕ) : ℕ := (row n).getD k 0

lemma length_go (m : ℕ) (r : List ℕ) (prev k : ℕ) : (go m r prev k).length = r.length + 1 := by
  induction r generalizing prev k with
  | nil => rfl
  | cons a as ih => simp [ih]

lemma length_row (n : ℕ) : (row n).length = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | m + 2, ih => rw [row_succ_succ, length_go, ih (m + 1) (by omega)]

/-- Entry `i` of one pass. -/
lemma getD_go (m : ℕ) (r : List ℕ) (prev k i : ℕ) :
    (go m r prev k).getD i 0 = (k + i) * r.getD i 0 + (m + 2 - (k + i)) * (prev :: r).getD i 0 := by
  induction r generalizing prev k i with
  | nil =>
    rcases i with _ | i
    · simp
    · simp
  | cons a as ih =>
    rcases i with _ | i
    · simp
    · rw [go_cons, List.getD_cons_succ, ih, List.getD_cons_succ, List.getD_cons_succ,
        show k + 1 + i = k + (i + 1) by omega]

lemma getD_of_length_le : ∀ (l : List ℕ) (i : ℕ), l.length ≤ i → l.getD i 0 = 0
  | [], _, _ => by simp
  | _ :: _, 0, h => absurd h (by simp)
  | _ :: as, i + 1, h => by
    rw [List.getD_cons_succ]; exact getD_of_length_le as i (by simpa using h)

/-- Initial value. -/
theorem E_one_zero : E 1 0 = 1 := rfl

/-- `E(n,k) = 0` for `k ≥ n`. -/
theorem E_eq_zero_of_le {n k : ℕ} (h : n ≤ k) : E n k = 0 :=
  getD_of_length_le _ _ (by rw [length_row]; exact h)

/-- `E(m+1,0) = E(m,0)` for `m ≥ 1` (so `E(n,0) = 1` for all `n ≥ 1`). -/
theorem E_succ_zero {m : ℕ} (hm : 1 ≤ m) : E (m + 1) 0 = E m 0 := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold E
  rw [show m + 1 + 1 = m + 2 from rfl, row_succ_succ, getD_go]
  simp

/-- The Eulerian recurrence `E(m+1,k) = (k+1) E(m,k) + (m+1-k) E(m,k-1)` for `m, k ≥ 1`. -/
theorem E_succ {m k : ℕ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    E (m + 1) k = (k + 1) * E m k + (m + 1 - k) * E m (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  unfold E
  rw [show m + 1 + 1 = m + 2 from rfl, row_succ_succ, getD_go, List.getD_cons_succ,
    show 1 + (k + 1) = k + 1 + 1 by omega, show m + 1 + 2 - (k + 1 + 1) = m + 1 + 1 - (k + 1) by omega,
    show k + 1 - 1 = k by omega]

-- sanity checks against the classical small rows
example : row 4 = [1, 11, 11, 1] := by decide +kernel
example : E 5 2 = 66 := by decide +kernel
example : row 5 = [1, 26, 66, 26, 1] := by decide +kernel
example : (row 7).sum = Nat.factorial 7 := by decide +kernel

/-! ### Kernel evaluation at `n = 669, 671` -/

/-- `c_669 < 333/106`, i.e. `106 · 669! < 333 · 670 · (E(669,334) - E(669,333))`. -/
theorem c669_lt :
    106 * Nat.factorial 669 < 333 * (669 + 1) * (E 669 334 - E 669 (334 - 1)) := by
  decide +kernel

/-- `355/113 < c_671`, i.e. `355 · 672 · (E(671,335) - E(671,334)) < 113 · 671!`. -/
theorem c671_gt :
    355 * (671 + 1) * (E 671 335 - E 671 (335 - 1)) < 113 * Nat.factorial 671 := by
  decide +kernel

/-- The central differences are positive (so `c_n` is well defined and positive). -/
theorem diffs_pos : E 669 (334 - 1) < E 669 334 ∧ E 671 (335 - 1) < E 671 335 := by
  decide +kernel

/-- Row sums `∑_k E(n,k) = n!` for the two rows used (consistency check). -/
theorem rowsum669 : (row 669).sum = Nat.factorial 669 := by
  decide +kernel

theorem rowsum671 : (row 671).sum = Nat.factorial 671 := by
  decide +kernel

/-! ### The angle comparison -/

open Real

/-- The classical rational bounds `333/106 < π < 355/113`. -/
theorem pi_bracket : (333 : ℝ) / 106 < π ∧ π < 355 / 113 := by
  constructor
  · have := Real.pi_gt_d6   -- 3.141592 < π
    norm_num at this ⊢
    linarith
  · have := Real.pi_lt_d20   -- π < 3.14159265358979323847
    norm_num at this ⊢
    linarith

/-- `c_n` of Lemma 3.15 and Remark 3.16, with the index `k = (n-1)/2` passed explicitly:
`c_n = n! / ((n+1) (E(n,k) - E(n,k-1)))`. -/
noncomputable def cn (n k : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) / (((n : ℝ) + 1) * ((E n k : ℝ) - (E n (k - 1) : ℝ)))

/-- From the integer inequality to `c_n < p/q` (generic in `n`, so that no factorial is ever
evaluated outside the kernel checks above). -/
lemma cn_lt_of_nat {n k p q : ℕ} (hq : 0 < q) (hd : E n (k - 1) < E n k)
    (h : q * n.factorial < p * (n + 1) * (E n k - E n (k - 1))) :
    cn n k < (p : ℝ) / q := by
  have hlt : (E n (k - 1) : ℝ) < E n k := by exact_mod_cast hd
  have hR : (q : ℝ) * n.factorial < p * ((n : ℝ) + 1) * ((E n k : ℝ) - E n (k - 1)) := by
    have := (Nat.cast_lt (α := ℝ)).2 h
    push_cast [Nat.cast_sub hd.le] at this
    exact this
  have hpos : 0 < ((n : ℝ) + 1) * ((E n k : ℝ) - E n (k - 1)) :=
    mul_pos (by positivity) (by linarith)
  unfold cn
  rw [div_lt_div_iff₀ hpos (by exact_mod_cast hq)]
  linarith

lemma lt_cn_of_nat {n k p q : ℕ} (hq : 0 < q) (hd : E n (k - 1) < E n k)
    (h : p * (n + 1) * (E n k - E n (k - 1)) < q * n.factorial) :
    (p : ℝ) / q < cn n k := by
  have hlt : (E n (k - 1) : ℝ) < E n k := by exact_mod_cast hd
  have hR : p * ((n : ℝ) + 1) * ((E n k : ℝ) - E n (k - 1)) < (q : ℝ) * n.factorial := by
    have := (Nat.cast_lt (α := ℝ)).2 h
    push_cast [Nat.cast_sub hd.le] at this
    exact this
  have hpos : 0 < ((n : ℝ) + 1) * ((E n k : ℝ) - E n (k - 1)) :=
    mul_pos (by positivity) (by linarith)
  unfold cn
  rw [div_lt_div_iff₀ (by exact_mod_cast hq) hpos]
  linarith

lemma cn_pos {n k : ℕ} (hd : E n (k - 1) < E n k) : 0 < cn n k := by
  have hlt : (E n (k - 1) : ℝ) < E n k := by exact_mod_cast hd
  unfold cn
  apply div_pos (by exact_mod_cast Nat.factorial_pos n)
  exact mul_pos (by positivity) (by linarith)

theorem c669_lt_pi : cn 669 334 < π := by
  have h := cn_lt_of_nat (p := 333) (q := 106) (by norm_num) diffs_pos.1 c669_lt
  have hpi : ((333 : ℕ) : ℝ) / ((106 : ℕ) : ℝ) < π := by exact_mod_cast pi_bracket.1
  exact h.trans hpi

theorem pi_lt_c671 : π < cn 671 335 := by
  have h := lt_cn_of_nat (p := 355) (q := 113) (by norm_num) diffs_pos.2 c671_gt
  have hpi : π < ((355 : ℕ) : ℝ) / ((113 : ℕ) : ℝ) := by exact_mod_cast pi_bracket.2
  exact hpi.trans h

lemma cn669_pos : 0 < cn 669 334 := cn_pos diffs_pos.1

/-- **Remark 3.16, Eq. (91).**  With `α_n = 2 arccot(c_n) = 2 arctan(1/c_n)` and
`ϑ_E = 2 arccot(π) = 2 arctan(1/π)`: `α_671 < ϑ_E < α_669`. -/
theorem angle_bracket :
    2 * arctan (1 / cn 671 335) < 2 * arctan (1 / π) ∧
    2 * arctan (1 / π) < 2 * arctan (1 / cn 669 334) := by
  constructor
  · have : 1 / cn 671 335 < 1 / π := one_div_lt_one_div_of_lt Real.pi_pos pi_lt_c671
    linarith [Real.arctan_strictMono this]
  · have : 1 / π < 1 / cn 669 334 := one_div_lt_one_div_of_lt cn669_pos c669_lt_pi
    linarith [Real.arctan_strictMono this]

end EulerianCert.Bracket
