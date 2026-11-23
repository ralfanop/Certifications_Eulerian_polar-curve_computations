import Mathlib

/-! # Manuscript 12, Lemma 5.12: finite propagation of the bilateral Jacobi operator

For bilateral bonds `u_m ∈ [0, 1/2]`, `J(u)_{m,m-1} = J(u)_{m-1,m} = u_m`. The columns
`J^n e_l` vanish at distance greater than `n` from `l` (`col_eq_zero_far`), and have
squared norm at most one (`col_norm_sq_le`), hence entries of modulus at most one
(`abs_col_le_one`). These are the two facts on `(J^n)_{kl}` used in the proof of the
propagation estimate (156). -/

namespace UniformLanczos.Lemma512Propagation

open Finset

/-- The column `J(u)^n e_l`: `(J v)_k = u_k v_{k-1} + u_{k+1} v_{k+1}`. -/
noncomputable def col (u : ℤ → ℝ) (l : ℤ) : ℕ → ℤ → ℝ
  | 0 => fun k => if k = l then 1 else 0
  | n + 1 => fun k => u k * col u l n (k - 1) + u (k + 1) * col u l n (k + 1)

theorem col_eq_zero_far (u : ℤ → ℝ) (l : ℤ) :
    ∀ n : ℕ, ∀ k : ℤ, (n : ℤ) < |k - l| → col u l n k = 0 := by
  intro n
  induction n with
  | zero =>
    intro k hk
    simp only [col]
    rw [if_neg]
    intro h; rw [h, sub_self, abs_zero] at hk; simp at hk
  | succ n ih =>
    intro k hk
    simp only [col]
    push_cast at hk
    rcases lt_abs.mp hk with h | h
    · rw [ih (k - 1) (lt_abs.mpr (Or.inl (by linarith))),
        ih (k + 1) (lt_abs.mpr (Or.inl (by linarith)))]
      ring
    · rw [ih (k - 1) (lt_abs.mpr (Or.inr (by linarith))),
        ih (k + 1) (lt_abs.mpr (Or.inr (by linarith)))]
      ring

/-- The window `[l-R, l+R]`. -/
def win (l : ℤ) (R : ℕ) : Finset ℤ := Finset.Icc (l - R) (l + R)

/-- Sum of `f(k ± 1)` over a window, compared with the sum of `f` over the window widened
by one, for nonnegative `f`. -/
theorem sum_shift_le (f : ℤ → ℝ) (hf : ∀ k, 0 ≤ f k) (l : ℤ) (R : ℕ) (e : ℤ)
    (he : e = 1 ∨ e = -1) :
    ∑ k ∈ win l R, f (k + e) ≤ ∑ k ∈ win l (R + 1), f k := by
  have hinj : ∀ x ∈ win l R, ∀ y ∈ win l R, x + e = y + e → x = y := by
    intro x _ y _ h; linarith
  rw [← Finset.sum_image hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    simp only [win, Finset.mem_Icc] at hk ⊢
    push_cast at hk ⊢
    rcases he with rfl | rfl <;> constructor <;> linarith [hk.1, hk.2]
  · intro i _ _; exact hf i

/-- **Column norm.** For bonds in `[0, 1/2]`, `Σ_k (J^n e_l)_k² ≤ 1`, the sum being over any
window `[l-R, l+R]` with `R ≥ n`. -/
theorem col_norm_sq_le (u : ℤ → ℝ) (hu : ∀ m, 0 ≤ u m ∧ u m ≤ 1 / 2) (l : ℤ) :
    ∀ n : ℕ, ∀ R : ℕ, n ≤ R → ∑ k ∈ win l R, col u l n k ^ 2 ≤ 1 := by
  intro n
  induction n with
  | zero =>
    intro R _
    simp only [col]
    rw [Finset.sum_eq_single l]
    · simp
    · intro k _ hk; simp [hk]
    · intro hl; exfalso; apply hl
      simp only [win, Finset.mem_Icc]; constructor <;> linarith [(Nat.cast_nonneg R : (0:ℤ) ≤ R)]
  | succ n ih =>
    intro R hR
    -- outside the window of radius `n` the column vanishes, so wider windows give the same sum
    have hwide : ∀ S : ℕ, n ≤ S → ∑ k ∈ win l S, col u l n k ^ 2 =
        ∑ k ∈ win l n, col u l n k ^ 2 := by
      intro S hS
      symm
      apply Finset.sum_subset
      · intro k hk
        simp only [win, Finset.mem_Icc] at hk ⊢
        have : (n:ℤ) ≤ S := by exact_mod_cast hS
        constructor <;> linarith [hk.1, hk.2]
      · intro k _ hk
        have hfar : (n:ℤ) < |k - l| := by
          simp only [win, Finset.mem_Icc, not_and_or, not_le] at hk
          rw [lt_abs]; rcases hk with h | h
          · right; linarith
          · left; linarith
        rw [col_eq_zero_far u l n k hfar]; ring
    have hpt : ∀ k, col u l (n + 1) k ^ 2 ≤
        col u l n (k + (-1)) ^ 2 / 2 + col u l n (k + 1) ^ 2 / 2 := by
      intro k
      simp only [col]
      have h1 := hu k
      have h2 := hu (k + 1)
      have hk1 : k - 1 = k + (-1) := by ring
      rw [hk1]
      set a := col u l n (k + (-1))
      set b := col u l n (k + 1)
      obtain ⟨h1a, h1b⟩ := h1
      obtain ⟨h2a, h2b⟩ := h2
      have hk2 : u k ^ 2 ≤ 1 / 4 := by nlinarith
      have hk3 : u (k + 1) ^ 2 ≤ 1 / 4 := by nlinarith
      have hua : (u k * a) ^ 2 ≤ a ^ 2 / 4 := by
        rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right hk2 (sq_nonneg a)]
      have hub : (u (k + 1) * b) ^ 2 ≤ b ^ 2 / 4 := by
        rw [mul_pow]; nlinarith [mul_le_mul_of_nonneg_right hk3 (sq_nonneg b)]
      nlinarith [sq_nonneg (u k * a - u (k + 1) * b)]
    obtain ⟨R', rfl⟩ : ∃ R', R = R' + 1 := ⟨R - 1, by omega⟩
    have hsq : ∀ k, 0 ≤ col u l n k ^ 2 := fun k => sq_nonneg _
    have s1 := sum_shift_le (fun k => col u l n k ^ 2) hsq l R' (-1) (Or.inr rfl)
    have s2 := sum_shift_le (fun k => col u l n k ^ 2) hsq l R' 1 (Or.inl rfl)
    -- the window of radius `R'+1` for `J^{n+1} e_l`: use radius `R'` plus vanishing at the edges
    have hedge : ∑ k ∈ win l (R' + 1), col u l (n + 1) k ^ 2 =
        ∑ k ∈ win l R', col u l (n + 1) k ^ 2 + ((col u l (n + 1) (l - (R' + 1))) ^ 2 +
          (col u l (n + 1) (l + (R' + 1))) ^ 2) := by
      have hW : win l (R' + 1) = insert (l - (R' + 1 : ℕ)) (insert (l + (R' + 1 : ℕ)) (win l R')) := by
        ext k; simp only [win, Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
      rw [hW, Finset.sum_insert, Finset.sum_insert]
      · push_cast; ring
      · simp only [win, Finset.mem_Icc]; push_cast; omega
      · simp only [win, Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
    by_cases hnR : n + 1 ≤ R'
    · -- the edges are far from `l`
      have e1 : col u l (n + 1) (l - (R' + 1)) = 0 := by
        apply col_eq_zero_far; push_cast
        rw [show l - (↑R' + 1) - l = -(↑R' + 1) by ring, abs_neg,
          abs_of_pos (by positivity)]
        have : ((n + 1 : ℕ) : ℤ) ≤ R' := by exact_mod_cast hnR
        push_cast at this; linarith
      have e2 : col u l (n + 1) (l + (R' + 1)) = 0 := by
        apply col_eq_zero_far; push_cast
        rw [show l + (↑R' + 1) - l = ↑R' + 1 by ring, abs_of_pos (by positivity)]
        have : ((n + 1 : ℕ) : ℤ) ≤ R' := by exact_mod_cast hnR
        push_cast at this; linarith
      rw [hedge, e1, e2]
      have hS : ∑ k ∈ win l R', col u l (n + 1) k ^ 2 ≤
          (∑ k ∈ win l (R' + 1), col u l n k ^ 2) / 2 +
            (∑ k ∈ win l (R' + 1), col u l n k ^ 2) / 2 := by
        calc ∑ k ∈ win l R', col u l (n + 1) k ^ 2
            ≤ ∑ k ∈ win l R', (col u l n (k + (-1)) ^ 2 / 2 + col u l n (k + 1) ^ 2 / 2) :=
              Finset.sum_le_sum fun k _ => hpt k
          _ = (∑ k ∈ win l R', col u l n (k + (-1)) ^ 2) / 2 +
                (∑ k ∈ win l R', col u l n (k + 1) ^ 2) / 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
          _ ≤ _ := by linarith
      have hih := ih (R' + 1) (by omega)
      linarith
    · -- `R' = n`: the window of radius `n+1` is the natural one
      have hR' : R' = n := by omega
      subst hR'
      have hS : ∑ k ∈ win l (R' + 1), col u l (R' + 1) k ^ 2 ≤
          (∑ k ∈ win l (R' + 2), col u l R' k ^ 2) / 2 +
            (∑ k ∈ win l (R' + 2), col u l R' k ^ 2) / 2 := by
        have t1 := sum_shift_le (fun k => col u l R' k ^ 2) hsq l (R' + 1) (-1) (Or.inr rfl)
        have t2 := sum_shift_le (fun k => col u l R' k ^ 2) hsq l (R' + 1) 1 (Or.inl rfl)
        calc ∑ k ∈ win l (R' + 1), col u l (R' + 1) k ^ 2
            ≤ ∑ k ∈ win l (R' + 1), (col u l R' (k + (-1)) ^ 2 / 2 +
                col u l R' (k + 1) ^ 2 / 2) := Finset.sum_le_sum fun k _ => hpt k
          _ = (∑ k ∈ win l (R' + 1), col u l R' (k + (-1)) ^ 2) / 2 +
                (∑ k ∈ win l (R' + 1), col u l R' (k + 1) ^ 2) / 2 := by
              rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
          _ ≤ _ := by linarith
      have hih := ih (R' + 2) (by omega)
      linarith

/-- **Entries of `J^n`.** For bonds in `[0, 1/2]`, `|(J^n)_{kl}| ≤ 1`. -/
theorem abs_col_le_one (u : ℤ → ℝ) (hu : ∀ m, 0 ≤ u m ∧ u m ≤ 1 / 2) (l : ℤ) (n : ℕ)
    (k : ℤ) : |col u l n k| ≤ 1 := by
  by_cases hk : (n : ℤ) < |k - l|
  · rw [col_eq_zero_far u l n k hk]; simp
  · push_neg at hk
    have hmem : k ∈ win l n := by
      simp only [win, Finset.mem_Icc]
      rcases abs_le.mp hk with ⟨h1, h2⟩
      constructor <;> linarith
    have hs := col_norm_sq_le u hu l n n le_rfl
    have hsingle := Finset.single_le_sum (f := fun k => col u l n k ^ 2)
      (fun k _ => sq_nonneg _) hmem
    have : col u l n k ^ 2 ≤ 1 := le_trans hsingle hs
    exact (sq_le_one_iff_abs_le_one _).mp this

/-! ## The exponential `e^{itJ}`: entries and the propagation estimate (156) -/

/-- The entry `(e^{itJ})_{kl} = Σ_n (it)^n/n! (J^n)_{kl}`. -/
noncomputable def expEntry (u : ℤ → ℝ) (l k : ℤ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (Complex.I * t) ^ n / (n.factorial : ℂ) * (col u l n k : ℂ)

theorem norm_term (u : ℤ → ℝ) (l k : ℤ) (t : ℝ) (n : ℕ) :
    ‖(Complex.I * t) ^ n / (n.factorial : ℂ) * (col u l n k : ℂ)‖ =
      |t| ^ n / n.factorial * |col u l n k| := by
  rw [norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]

/-- **Tail of the exponential series.** With `d = |k-l|`,
`|(e^{itJ})_{kl}| ≤ 2 e^{4|t|} 2^{-d}`, since `(J^n)_{kl} = 0` for `n < d` and `|(J^n)_{kl}| ≤ 1`. -/
theorem expEntry_tail (u : ℤ → ℝ) (hu : ∀ m, 0 ≤ u m ∧ u m ≤ 1 / 2) (l k : ℤ) (t : ℝ) :
    ‖expEntry u l k t‖ ≤ 2 * Real.exp (4 * |t|) * (1 / 2) ^ (|k - l|).toNat := by
  set d := (|k - l|).toNat
  have hd : ((d : ℕ) : ℤ) = |k - l| := Int.toNat_of_nonneg (abs_nonneg _)
  set g : ℕ → ℝ := fun n => Real.exp (4 * |t|) * (1 / 2) ^ d * (1 / 2) ^ n
  have hgs : Summable g :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm : ∀ n, ‖(Complex.I * t) ^ n / (n.factorial : ℂ) * (col u l n k : ℂ)‖ ≤ g n := by
    intro n
    rw [norm_term]
    by_cases hn : n < d
    · have : (n : ℤ) < |k - l| := by rw [← hd]; exact_mod_cast hn
      rw [col_eq_zero_far u l n k this, abs_zero, mul_zero]
      positivity
    · push_neg at hn
      have h1 : |t| ^ n / n.factorial ≤ Real.exp (4 * |t|) * (1 / 4) ^ n := by
        have h := Real.pow_div_factorial_le_exp (4 * |t|) (by positivity) n
        rw [mul_pow] at h
        have h4 : (0:ℝ) < 4 ^ n := by positivity
        rw [div_pow, one_pow, ← div_eq_mul_one_div, le_div_iff₀ h4]
        calc |t| ^ n / n.factorial * 4 ^ n = 4 ^ n * |t| ^ n / n.factorial := by ring
          _ ≤ Real.exp (4 * |t|) := h
      have h2 : (1 / 4 : ℝ) ^ n ≤ (1 / 2) ^ d * (1 / 2) ^ n := by
        rw [show (1 / 4 : ℝ) = (1 / 2) * (1 / 2) by norm_num, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) (by positivity)
      have hc := abs_col_le_one u hu l n k
      calc |t| ^ n / n.factorial * |col u l n k| ≤ |t| ^ n / n.factorial * 1 :=
            mul_le_mul_of_nonneg_left hc (by positivity)
        _ ≤ Real.exp (4 * |t|) * (1 / 4) ^ n := by rw [mul_one]; exact h1
        _ ≤ Real.exp (4 * |t|) * ((1 / 2) ^ d * (1 / 2) ^ n) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = g n := by simp only [g]; ring
  have hns : Summable fun n => ‖(Complex.I * t) ^ n / (n.factorial : ℂ) * (col u l n k : ℂ)‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hgs
  calc ‖expEntry u l k t‖ ≤ ∑' n, ‖(Complex.I * t) ^ n / (n.factorial : ℂ) * (col u l n k : ℂ)‖ :=
        norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n, g n := hns.tsum_le_tsum hterm hgs
    _ = 2 * Real.exp (4 * |t|) * (1 / 2) ^ d := by
        simp only [g]
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
        norm_num; ring

/-- `(1+d)^N e^{-a d} ≤ e^a N!/a^N` for `d ≥ 0`, `a > 0`. -/
theorem poly_exp_le {a d : ℝ} (ha : 0 < a) (hd : 0 ≤ d) (N : ℕ) :
    (1 + d) ^ N * Real.exp (-(a * d)) ≤ Real.exp a * N.factorial / a ^ N := by
  have hy := Real.pow_div_factorial_le_exp (a * (1 + d)) (by positivity) N
  have haN : 0 < a ^ N := pow_pos ha N
  have hf : (0:ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [mul_pow, div_le_iff₀ hf] at hy
  rw [le_div_iff₀ haN]
  have he : Real.exp (-(a * d)) = Real.exp a * Real.exp (-(a * (1 + d))) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  have hpos : 0 < Real.exp (a * (1 + d)) := Real.exp_pos _
  have hinv : Real.exp (-(a * (1 + d))) * Real.exp (a * (1 + d)) = 1 := by
    rw [← Real.exp_add]; simp
  have hexp_nonneg : 0 ≤ Real.exp (-(a * (1 + d))) := (Real.exp_pos _).le
  calc (1 + d) ^ N * (Real.exp a * Real.exp (-(a * (1 + d)))) * a ^ N
      = Real.exp a * Real.exp (-(a * (1 + d))) * (a ^ N * (1 + d) ^ N) := by ring
    _ ≤ Real.exp a * Real.exp (-(a * (1 + d))) * (Real.exp (a * (1 + d)) * N.factorial) := by
        apply mul_le_mul_of_nonneg_left hy; positivity
    _ = Real.exp a * N.factorial * (Real.exp (-(a * (1 + d))) * Real.exp (a * (1 + d))) := by
        ring
    _ = Real.exp a * N.factorial := by rw [hinv, mul_one]

/-- The decay rate `a = log 2 - 1/2 > 0` of the tail beyond `d ≥ 8|t|`. -/
noncomputable def rate : ℝ := Real.log 2 - 1 / 2

theorem rate_pos : 0 < rate := by
  unfold rate
  have := Real.add_one_lt_exp (by norm_num : (1/2:ℝ) ≠ 0)
  have h2 : Real.exp (1 / 2) < 2 := by
    have := Real.exp_one_lt_d9
    have h : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    nlinarith [Real.exp_pos (1 / 2)]
  have := Real.log_lt_log (Real.exp_pos _) h2
  rw [Real.log_exp] at this
  linarith

/-- The constant `C_N` of (156). -/
noncomputable def CN (N : ℕ) : ℝ := 8 ^ N + 2 * Real.exp rate * N.factorial / rate ^ N

/-- **Propagation estimate (156).** For bonds in `[0, 1/2]`,
`|(e^{itJ})_{kl}| ≤ C_N (1+|t|)^N/(1+|k-l|)^N`. The bound `|(e^{itJ})_{kl}| ≤ 1`, from the
unitarity of `e^{itJ}` for the bounded self-adjoint `J` (a published result cited), enters as
the premise `hunit`. -/
theorem propagation (u : ℤ → ℝ) (hu : ∀ m, 0 ≤ u m ∧ u m ≤ 1 / 2) (l k : ℤ) (t : ℝ)
    (hunit : ‖expEntry u l k t‖ ≤ 1) (N : ℕ) :
    ‖expEntry u l k t‖ ≤ CN N * (1 + |t|) ^ N / (1 + |(k:ℝ) - l|) ^ N := by
  set D : ℝ := |(k:ℝ) - l|
  have hD0 : 0 ≤ D := abs_nonneg _
  have hDpos : 0 < (1 + D) ^ N := by positivity
  have ht1 : 1 ≤ (1 + |t|) ^ N := one_le_pow₀ (by linarith [abs_nonneg t])
  have hC1 : 8 ^ N ≤ CN N := by
    unfold CN; have := rate_pos; have : (0:ℝ) ≤ 2 * Real.exp rate * N.factorial / rate ^ N := by
      positivity
    linarith
  rw [le_div_iff₀ hDpos]
  by_cases hfar : 8 * |t| ≤ D
  · -- far: the tail bound, `2 e^{4|t|} 2^{-d} ≤ 2 e^{-a d}`
    have htail := expEntry_tail u hu l k t
    have hd : (((|k - l|).toNat : ℕ) : ℝ) = D := by
      have h := Int.toNat_of_nonneg (abs_nonneg (k - l))
      have : ((((|k - l|).toNat : ℕ) : ℤ) : ℝ) = ((|k - l| : ℤ) : ℝ) := by rw [h]
      rw [Int.cast_natCast] at this; rw [this]; push_cast; rfl
    have hpow : (1 / 2 : ℝ) ^ (|k - l|).toNat = Real.exp (-(Real.log 2 * D)) := by
      rw [← hd, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.log_div one_ne_zero
        two_ne_zero, Real.log_one]
      congr 1; ring
    have hexp : Real.exp (4 * |t|) * Real.exp (-(Real.log 2 * D)) ≤ Real.exp (-(rate * D)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; unfold rate; nlinarith
    have hpoly := poly_exp_le rate_pos hD0 N
    calc ‖expEntry u l k t‖ * (1 + D) ^ N
        ≤ 2 * Real.exp (4 * |t|) * (1 / 2) ^ (|k - l|).toNat * (1 + D) ^ N :=
          mul_le_mul_of_nonneg_right htail hDpos.le
      _ ≤ 2 * Real.exp (-(rate * D)) * (1 + D) ^ N := by
          rw [hpow]; apply mul_le_mul_of_nonneg_right _ hDpos.le; nlinarith
      _ = 2 * ((1 + D) ^ N * Real.exp (-(rate * D))) := by ring
      _ ≤ 2 * (Real.exp rate * N.factorial / rate ^ N) := by linarith
      _ ≤ CN N := by unfold CN; have : (0:ℝ) ≤ 8 ^ N := by positivity
                     have : 2 * (Real.exp rate * N.factorial / rate ^ N) =
                       2 * Real.exp rate * N.factorial / rate ^ N := by ring
                     linarith
      _ ≤ CN N * (1 + |t|) ^ N := by
          have : 0 ≤ CN N := le_trans (by positivity) hC1
          nlinarith
  · -- near: unitarity and `1 + D ≤ 8 (1 + |t|)`
    push_neg at hfar
    have hnear : (1 + D) ^ N ≤ 8 ^ N * (1 + |t|) ^ N := by
      rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); nlinarith [abs_nonneg t]
    calc ‖expEntry u l k t‖ * (1 + D) ^ N ≤ 1 * (1 + D) ^ N :=
          mul_le_mul_of_nonneg_right hunit hDpos.le
      _ ≤ 8 ^ N * (1 + |t|) ^ N := by rw [one_mul]; exact hnear
      _ ≤ CN N * (1 + |t|) ^ N := mul_le_mul_of_nonneg_right hC1 (by positivity)

end UniformLanczos.Lemma512Propagation

#print axioms UniformLanczos.Lemma512Propagation.col_eq_zero_far
#print axioms UniformLanczos.Lemma512Propagation.sum_shift_le
#print axioms UniformLanczos.Lemma512Propagation.col_norm_sq_le
#print axioms UniformLanczos.Lemma512Propagation.abs_col_le_one
#print axioms UniformLanczos.Lemma512Propagation.expEntry_tail
#print axioms UniformLanczos.Lemma512Propagation.poly_exp_le
#print axioms UniformLanczos.Lemma512Propagation.rate_pos
#print axioms UniformLanczos.Lemma512Propagation.propagation
